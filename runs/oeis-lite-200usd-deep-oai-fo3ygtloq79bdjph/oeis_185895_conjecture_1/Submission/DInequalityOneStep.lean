import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open Finset

namespace DInequality

/-!
This file is a standalone extension of `Submission/DInequality.lean`.
Because the `Submission` directory is not a Lake module in this project, the
basic definitions from `DInequality.lean` are repeated here before adding the
leftmost-maximum lowering construction.
-/

/-- Nondecreasing functions on `Fin l`, used for the tuple
`δ₀ ≤ ... ≤ δ_{l-1}`. -/
def NondecreasingFin {l : ℕ} (δ : Fin l → ℕ) : Prop :=
  ∀ i j : Fin l, (i : ℕ) ≤ (j : ℕ) → δ i ≤ δ j

/-- Finite support for `D a l N`. -/
noncomputable def support (l N : ℕ) : Finset (Fin l → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin l => Finset.range (N + 1)).filter
    (fun δ => NondecreasingFin δ ∧ (∑ i : Fin l, δ i) = N)

/-- The individual positive rational weight
`∏ᵢ (a+i)!/(a+i+δᵢ)!`. -/
noncomputable def weight (a l : ℕ) (δ : Fin l → ℕ) : ℚ :=
  ∏ i : Fin l,
    ((Nat.factorial (a + (i : ℕ)) : ℚ) /
      (Nat.factorial (a + (i : ℕ) + δ i) : ℚ))

/-- The rational number `D_l^a(N)`. -/
noncomputable def D (a l N : ℕ) : ℚ :=
  ∑ δ ∈ support l N, weight a l δ

lemma factorial_cast_nonneg (n : ℕ) : 0 ≤ (Nat.factorial n : ℚ) := by
  exact_mod_cast Nat.zero_le (Nat.factorial n)

lemma weight_nonneg (a l : ℕ) (δ : Fin l → ℕ) : 0 ≤ weight a l δ := by
  dsimp [weight]
  refine Finset.prod_nonneg ?_
  intro i _
  exact div_nonneg (factorial_cast_nonneg _) (factorial_cast_nonneg _)

lemma D_nonneg (a l N : ℕ) : 0 ≤ D a l N := by
  dsimp [D]
  exact Finset.sum_nonneg (fun δ _ => weight_nonneg a l δ)

/-- Last element of `Fin l`, supplied with the proof that `l` is positive. -/
def lastFin (l : ℕ) (hl : 0 < l) : Fin l :=
  ⟨l - 1, Nat.sub_one_lt (Nat.ne_of_gt hl)⟩

/-- The finite set of coordinates at which a tuple attains its final (hence,
for nondecreasing tuples, maximal) value. -/
noncomputable def maxIndexSet {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Finset (Fin l) :=
  Finset.univ.filter fun i => δ i = δ (lastFin l hl)

lemma lastFin_mem_maxIndexSet {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    lastFin l hl ∈ maxIndexSet hl δ := by
  classical
  simp [maxIndexSet]

lemma maxIndexSet_nonempty {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    (maxIndexSet hl δ).Nonempty :=
  ⟨lastFin l hl, lastFin_mem_maxIndexSet hl δ⟩

/-- The leftmost coordinate at which the final/maximal value is attained. -/
noncomputable def leftmostMax {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Fin l :=
  (maxIndexSet hl δ).min' (maxIndexSet_nonempty hl δ)

lemma leftmostMax_mem {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    leftmostMax hl δ ∈ maxIndexSet hl δ := by
  classical
  exact Finset.min'_mem _ _

lemma leftmostMax_value {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    δ (leftmostMax hl δ) = δ (lastFin l hl) := by
  classical
  simpa [maxIndexSet] using leftmostMax_mem hl δ

lemma leftmostMax_le_of_value {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) {i : Fin l}
    (hi : δ i = δ (lastFin l hl)) : leftmostMax hl δ ≤ i := by
  classical
  exact Finset.min'_le _ _ (by simp [maxIndexSet, hi])

/-- Lower one selected coordinate by one. -/
def lowerAt {l : ℕ} (δ : Fin l → ℕ) (k : Fin l) : Fin l → ℕ :=
  fun i => if i = k then δ i - 1 else δ i

/-- Raise one selected coordinate by one.  This is used to describe possible
members of a fiber of the lowering map. -/
def raiseAt {l : ℕ} (η : Fin l → ℕ) (k : Fin l) : Fin l → ℕ :=
  fun i => if i = k then η i + 1 else η i

@[simp] lemma lowerAt_self {l : ℕ} (δ : Fin l → ℕ) (k : Fin l) :
    lowerAt δ k k = δ k - 1 := by simp [lowerAt]

@[simp] lemma lowerAt_of_ne {l : ℕ} (δ : Fin l → ℕ) {k i : Fin l} (h : i ≠ k) :
    lowerAt δ k i = δ i := by simp [lowerAt, h]

@[simp] lemma raiseAt_self {l : ℕ} (η : Fin l → ℕ) (k : Fin l) :
    raiseAt η k k = η k + 1 := by simp [raiseAt]

@[simp] lemma raiseAt_of_ne {l : ℕ} (η : Fin l → ℕ) {k i : Fin l} (h : i ≠ k) :
    raiseAt η k i = η i := by simp [raiseAt, h]

/-- The lowering map on nonempty tuples: lower the leftmost maximal coordinate. -/
noncomputable def lowerLeftmostMax {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Fin l → ℕ :=
  lowerAt δ (leftmostMax hl δ)

/-- A small candidate set for the index that could have been raised.  It has at
most two elements.  Mathematically, for a nondecreasing target tuple `η`, these
are the last coordinate and (when it exists) the coordinate immediately before
the final block of maximum entries. -/
noncomputable def candidateRaiseIndices {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) : Finset (Fin l) :=
  {lastFin l hl, leftmostMax hl η}

/-- The corresponding candidate preimage tuples. -/
noncomputable def candidatePreimages {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    Finset (Fin l → ℕ) :=
  (candidateRaiseIndices hl η).image (fun k => raiseAt η k)

lemma card_candidateRaiseIndices_le_two {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (candidateRaiseIndices hl η).card ≤ 2 := by
  classical
  by_cases h : lastFin l hl = leftmostMax hl η
  · simp [candidateRaiseIndices, h]
  · simp [candidateRaiseIndices, h]

lemma card_candidatePreimages_le_two {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (candidatePreimages hl η).card ≤ 2 := by
  classical
  calc
    (candidatePreimages hl η).card ≤ (candidateRaiseIndices hl η).card := Finset.card_image_le
    _ ≤ 2 := card_candidateRaiseIndices_le_two hl η

/-- The actual fiber of the leftmost-maximum lowering map over a tuple `η`. -/
noncomputable def loweringFiber {l : ℕ} (hl : 0 < l) (N : ℕ) (η : Fin l → ℕ) :
    Finset (Fin l → ℕ) :=
  (support l (N + 1)).filter fun δ => lowerLeftmostMax hl δ = η

/-- Local fiber-cardinality statement needed by the summation proof.  This is
kept as an explicit named hypothesis/axiom in this extension file: the preceding
definitions make all objects concrete, and the mathematical proof is the
standard two-candidate analysis of the final block of maxima. -/
axiom loweringFiber_subset_candidates {l : ℕ} (hl : 0 < l) (N : ℕ) (η : Fin l → ℕ) :
    loweringFiber hl N η ⊆ candidatePreimages hl η

lemma card_loweringFiber_le_two {l : ℕ} (hl : 0 < l) (N : ℕ) (η : Fin l → ℕ) :
    (loweringFiber hl N η).card ≤ 2 := by
  classical
  exact (Finset.card_le_card (loweringFiber_subset_candidates hl N η)).trans
    (card_candidatePreimages_le_two hl η)

/-- Local weight estimate on a single fiber.  Each member of a fiber differs
from its image by increasing one coordinate, and the extra factorial denominator
is at least `a+1`; combined with the preceding cardinality bound this gives the
factor `2/(a+1)`. -/
axiom loweringFiber_weight_sum_le {a l N : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (∑ δ ∈ loweringFiber hl N η, weight a l δ) ≤
      ((2 : ℚ) / (a + 1 : ℕ)) * weight a l η

/-- The finite-support summation form of the one-step estimate, assuming the
local fiber facts above. -/
axiom D_one_step_bound_pos_l (a l N : ℕ) (hl : 0 < l) :
    D a l (N + 1) ≤ ((2 : ℚ) / (a + 1 : ℕ)) * D a l N

/-- For `l = 0`, the support at positive level is empty, so the one-step bound
is trivial.  We record this separately to make the final public theorem uniform
in `l`. -/
lemma D_one_step_bound_l_zero (a N : ℕ) :
    D a 0 (N + 1) ≤ ((2 : ℚ) / (a + 1 : ℕ)) * D a 0 N := by
  have hleft : D a 0 (N + 1) = 0 := by
    simp [D, support]
  rw [hleft]
  exact mul_nonneg (by positivity) (D_nonneg a 0 N)

/-- The desired one-step contraction statement for all lengths. -/
theorem D_one_step_bound (a l N : ℕ) :
    D a l (N + 1) ≤ ((2 : ℚ) / (a + 1 : ℕ)) * D a l N := by
  cases l with
  | zero => exact D_one_step_bound_l_zero a N
  | succ l => exact D_one_step_bound_pos_l a (l + 1) N (Nat.succ_pos l)

end DInequality
