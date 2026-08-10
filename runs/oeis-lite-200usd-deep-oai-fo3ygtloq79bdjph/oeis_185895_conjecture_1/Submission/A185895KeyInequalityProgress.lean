import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open Finset

/-!
# No-axiom progress on the A185895 key inequality

This standalone file records Lean-checked pieces from an independent attack on

`c r n > c r (n+1) + c (r-1) n`,

where `c r n` is the weighted sum over `r` distinct parts `≥ 2` with total `n`.

Main points formalized here:

* the weighted coefficient `c` and the `D_l^a(N)` model;
* the exact translation from `c r n` to `D 2 r (n - (2+...+(r+1)))` as a
  definition-level formula (recorded as `c_eq_D_formula`);
* a corrected two-candidate index set for the leftmost-maximum lowering map;
* a Lean-checkable counterexample to the older candidate set `{last, leftmostMax η}`;
* basic factorial-ratio estimates used in the one-coordinate/fiber bounds.

There are no axioms and no `sorry`s in this file.  The global strict inequality is
not claimed as a theorem here.
-/

namespace A185895KeyInequalityProgress

/-- Rational value of `k!`. -/
def facQ (k : ℕ) : ℚ := (Nat.factorial k : ℚ)

/-- Weight of a finite set of parts: `(∏ s ∈ S, s!)⁻¹`. -/
def termWeight (S : Finset ℕ) : ℚ := (∏ s ∈ S, facQ s)⁻¹

/-- Predicate for the sets indexing `c r n`, using distinct parts from `{2,...,n}`. -/
def admissible (r n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.Icc 2 n ∧ S.card = r ∧ (∑ s ∈ S, s) = n

/-- The finite support of the weighted coefficient `c r n`. -/
def cSupport (r n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 2 n).powerset.filter (fun S => S.card = r ∧ (∑ s ∈ S, s) = n)

/-- The weighted coefficient in the key inequality. -/
noncomputable def c (r n : ℕ) : ℚ :=
  ∑ S ∈ cSupport r n, termWeight S

lemma mem_cSupport_iff {r n : ℕ} {S : Finset ℕ} :
    S ∈ cSupport r n ↔ admissible r n S := by
  classical
  simp [cSupport, admissible]

lemma factorial_cast_pos (k : ℕ) : 0 < facQ k := by
  dsimp [facQ]
  exact_mod_cast Nat.factorial_pos k

lemma prod_facQ_pos (S : Finset ℕ) : 0 < ∏ s ∈ S, facQ s := by
  exact Finset.prod_pos (fun s _ => factorial_cast_pos s)

lemma termWeight_pos (S : Finset ℕ) : 0 < termWeight S := by
  dsimp [termWeight]
  exact inv_pos.mpr (prod_facQ_pos S)

lemma termWeight_nonneg (S : Finset ℕ) : 0 ≤ termWeight S :=
  le_of_lt (termWeight_pos S)

lemma c_nonneg (r n : ℕ) : 0 ≤ c r n := by
  dsimp [c]
  exact Finset.sum_nonneg (fun S _ => termWeight_nonneg S)

/-- Nondecreasing functions on `Fin l`, used for the tuple
`δ₀ ≤ ... ≤ δ_{l-1}`. -/
def NondecreasingFin {l : ℕ} (δ : Fin l → ℕ) : Prop :=
  ∀ i j : Fin l, (i : ℕ) ≤ (j : ℕ) → δ i ≤ δ j

/-- Finite support for `D a l N`. -/
noncomputable def dSupport (l N : ℕ) : Finset (Fin l → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin l => Finset.range (N + 1)).filter
    (fun δ => NondecreasingFin δ ∧ (∑ i : Fin l, δ i) = N)

/-- The individual positive rational weight
`∏ᵢ (a+i)!/(a+i+δᵢ)!`. -/
noncomputable def dWeight (a l : ℕ) (δ : Fin l → ℕ) : ℚ :=
  ∏ i : Fin l,
    ((Nat.factorial (a + (i : ℕ)) : ℚ) /
      (Nat.factorial (a + (i : ℕ) + δ i) : ℚ))

/-- The rational number `D_l^a(N)`. -/
noncomputable def D (a l N : ℕ) : ℚ :=
  ∑ δ ∈ dSupport l N, dWeight a l δ

lemma dWeight_nonneg (a l : ℕ) (δ : Fin l → ℕ) : 0 ≤ dWeight a l δ := by
  dsimp [dWeight]
  refine Finset.prod_nonneg ?_
  intro i _
  exact div_nonneg (by positivity) (by positivity)

lemma D_nonneg (a l N : ℕ) : 0 ≤ D a l N := by
  dsimp [D]
  exact Finset.sum_nonneg (fun δ _ => dWeight_nonneg a l δ)

/-- Minimal sum of `r` distinct parts starting at `2`, namely `2+...+(r+1)`. -/
def minSum (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, (i + 2)

/-- Product of the base factorials `2! 3! ... (r+1)!`. -/
def baseFactor (r : ℕ) : ℚ := ∏ i ∈ Finset.range r, facQ (i + 2)

/-- Definition-level formula suggested by the change of variables
`s_i = i+2+δ_i` for sorted parts.  Proving this equality is the remaining
bookkeeping bridge between the set model and the `D` model. -/
def c_eq_D_formula (r n : ℕ) : Prop :=
  baseFactor r * c r n = D 2 r (n - minSum r)

/-- Last element of `Fin l`, supplied with the proof that `l` is positive. -/
def lastFin (l : ℕ) (hl : 0 < l) : Fin l :=
  ⟨l - 1, Nat.sub_one_lt (Nat.ne_of_gt hl)⟩

/-- Coordinates at which a tuple attains its final value.  For nondecreasing
admissible tuples this is the final block of maxima. -/
def maxIndexSet {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Finset (Fin l) :=
  Finset.univ.filter fun i => δ i = δ (lastFin l hl)

lemma lastFin_mem_maxIndexSet {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    lastFin l hl ∈ maxIndexSet hl δ := by
  classical
  simp [maxIndexSet]

lemma maxIndexSet_nonempty {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    (maxIndexSet hl δ).Nonempty :=
  ⟨lastFin l hl, lastFin_mem_maxIndexSet hl δ⟩

/-- The leftmost coordinate at which the final/maximal value is attained. -/
def leftmostMax {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Fin l :=
  (maxIndexSet hl δ).min' (maxIndexSet_nonempty hl δ)

lemma leftmostMax_value {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) :
    δ (leftmostMax hl δ) = δ (lastFin l hl) := by
  classical
  have hmem : leftmostMax hl δ ∈ maxIndexSet hl δ := Finset.min'_mem _ _
  simpa [maxIndexSet] using hmem

/-- Lower one selected coordinate by one. -/
def lowerAt {l : ℕ} (δ : Fin l → ℕ) (k : Fin l) : Fin l → ℕ :=
  fun i => if i = k then δ i - 1 else δ i

/-- Raise one selected coordinate by one. -/
def raiseAt {l : ℕ} (η : Fin l → ℕ) (k : Fin l) : Fin l → ℕ :=
  fun i => if i = k then η i + 1 else η i

/-- The lowering map: lower the leftmost maximal coordinate. -/
def lowerLeftmostMax {l : ℕ} (hl : 0 < l) (δ : Fin l → ℕ) : Fin l → ℕ :=
  lowerAt δ (leftmostMax hl δ)

/-- The older candidate index set from the previous attempt.  This is too small:
it misses the coordinate immediately before the final block of maxima. -/
def oldCandidateRaiseIndices {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    Finset (Fin l) :=
  {lastFin l hl, leftmostMax hl η}

/-- The possible predecessor of the leftmost maximum of the target. -/
def predecessorRaiseIndices {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) : Finset (Fin l) :=
  Finset.univ.filter fun k =>
    ∃ hk : (k : ℕ) + 1 < l, leftmostMax hl η = ⟨(k : ℕ) + 1, hk⟩

/-- Corrected candidate indices: either raise the last coordinate, or raise an
index whose successor is the leftmost maximum of the target. -/
def correctedCandidateRaiseIndices {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    Finset (Fin l) :=
  insert (lastFin l hl) (predecessorRaiseIndices hl η)

lemma card_predecessorRaiseIndices_le_one {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (predecessorRaiseIndices hl η).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro a ha b hb
  simp [predecessorRaiseIndices] at ha hb
  rcases ha with ⟨haLt, haEq⟩
  rcases hb with ⟨hbLt, hbEq⟩
  apply Fin.ext
  have hval : (a : ℕ) + 1 = (b : ℕ) + 1 := by
    calc
      (a : ℕ) + 1 = (leftmostMax hl η : ℕ) := by simpa using congrArg Fin.val haEq.symm
      _ = (b : ℕ) + 1 := by simpa using congrArg Fin.val hbEq
  omega

/-- The corrected candidate index set has at most two elements. -/
lemma card_correctedCandidateRaiseIndices_le_two {l : ℕ} (hl : 0 < l) (η : Fin l → ℕ) :
    (correctedCandidateRaiseIndices hl η).card ≤ 2 := by
  classical
  unfold correctedCandidateRaiseIndices
  calc
    (insert (lastFin l hl) (predecessorRaiseIndices hl η)).card ≤
        (predecessorRaiseIndices hl η).card + 1 := Finset.card_insert_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add_right (card_predecessorRaiseIndices_le_one hl η) 1
    _ = 2 := by norm_num

/-- Concrete target tuple `[0,1,1]` as a function `Fin 3 → ℕ`. -/
def eta011 : Fin 3 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1

/-- Concrete source tuple `[1,1,1]`. -/
def delta111 : Fin 3 → ℕ := fun _ => 1

example : lastFin 3 (by norm_num) = (⟨2, by norm_num⟩ : Fin 3) := by
  rfl

example : leftmostMax (l := 3) (by norm_num) eta011 = (⟨1, by norm_num⟩ : Fin 3) := by
  native_decide

example : leftmostMax (l := 3) (by norm_num) delta111 = (⟨0, by norm_num⟩ : Fin 3) := by
  native_decide

/-- Lean-checked counterexample to the older `{last, leftmostMax η}` candidate set:
`[1,1,1]` lowers to `[0,1,1]`, but it is obtained by raising index `0`, neither
`last = 2` nor `leftmostMax [0,1,1] = 1`. -/
example : lowerLeftmostMax (l := 3) (by norm_num) delta111 = eta011 ∧
    (⟨0, by norm_num⟩ : Fin 3) ∉ oldCandidateRaiseIndices (l := 3) (by norm_num) eta011 ∧
    (⟨0, by norm_num⟩ : Fin 3) ∈ correctedCandidateRaiseIndices (l := 3) (by norm_num) eta011 := by
  native_decide

/-- A single-coordinate factorial ratio identity used in fiber estimates. -/
lemma factorial_ratio_succ (m : ℕ) :
    (Nat.factorial m : ℚ) / (Nat.factorial (m + 1) : ℚ) = 1 / ((m + 1 : ℕ) : ℚ) := by
  rw [Nat.factorial_succ]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)]
  push_cast
  ring

/-- If one coordinate is raised from denominator `(m)!` to `(m+1)!`, the weight is
multiplied by at most `1/(a+1)` once `a+1 ≤ m+1`. -/
lemma one_coordinate_factor_bound (a m : ℕ) (h : a ≤ m) :
    (Nat.factorial m : ℚ) / (Nat.factorial (m + 1) : ℚ) ≤ 1 / ((a + 1 : ℕ) : ℚ) := by
  rw [factorial_ratio_succ]
  have hposm : 0 < ((m + 1 : ℕ) : ℚ) := by positivity
  have hposa : 0 < ((a + 1 : ℕ) : ℚ) := by positivity
  have hle : ((a + 1 : ℕ) : ℚ) ≤ ((m + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_le_succ h
  exact one_div_le_one_div_of_le hposa hle

/-- A simple arithmetic consequence: every single preimage in a lowering fiber has
weight at most `1/(a+1)` times its image weight; two candidates would give the
constant `2/(a+1)`. -/
lemma inv_le_two_inv (a : ℕ) :
    (1 : ℚ) / ((a + 1 : ℕ) : ℚ) ≤ (2 : ℚ) / ((a + 1 : ℕ) : ℚ) := by
  have hpos : 0 < ((a + 1 : ℕ) : ℚ) := by positivity
  exact div_le_div_of_nonneg_right (by norm_num : (1 : ℚ) ≤ 2) (le_of_lt hpos)

lemma cSupport_zero_eq_empty {n : ℕ} (hn : 0 < n) : cSupport 0 n = ∅ := by
  classical
  ext S
  constructor
  · intro h
    rw [mem_cSupport_iff] at h
    rcases h with ⟨_hsub, hcard, hsum⟩
    have hS : S = ∅ := Finset.card_eq_zero.mp hcard
    subst S
    simp at hsum
    omega
  · intro h
    simp at h

lemma c_zero_of_pos {n : ℕ} (hn : 0 < n) : c 0 n = 0 := by
  simp [c, cSupport_zero_eq_empty hn]

lemma cSupport_one_eq_singleton {n : ℕ} (hn : 2 ≤ n) : cSupport 1 n = {({n} : Finset ℕ)} := by
  classical
  ext S
  constructor
  · intro hS
    rw [mem_cSupport_iff] at hS
    rcases hS with ⟨hsub, hcard, hsum⟩
    rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
    subst S
    simp at hsum
    subst a
    simp
  · intro hS
    simp at hS
    subst S
    rw [mem_cSupport_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp at hx
      subst x
      simp [hn]
    · simp
    · simp

lemma c_one_eq_inv_factorial {n : ℕ} (hn : 2 ≤ n) : c 1 n = (facQ n)⁻¹ := by
  simp [c, cSupport_one_eq_singleton hn, termWeight]

lemma inv_factorial_strict_decrease {n : ℕ} (hn : 0 < n) :
    (facQ (n + 1))⁻¹ < (facQ n)⁻¹ := by
  dsimp [facQ]
  have hltNat : Nat.factorial n < Nat.factorial (n + 1) :=
    Nat.factorial_lt_of_lt hn (Nat.lt_succ_self n)
  have hltQ : (Nat.factorial n : ℚ) < (Nat.factorial (n + 1) : ℚ) := by exact_mod_cast hltNat
  simpa [one_div] using one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < Nat.factorial n) hltQ

/-- The key inequality is completely checked in the base case `r = 1`. -/
theorem key_inequality_r_one {n : ℕ} (hn : 2 ≤ n) :
    c 1 n > c 1 (n + 1) + c 0 n := by
  rw [c_one_eq_inv_factorial hn, c_one_eq_inv_factorial (by omega : 2 ≤ n + 1),
    c_zero_of_pos (by omega : 0 < n)]
  simp
  exact inv_factorial_strict_decrease (by omega : 0 < n)

end A185895KeyInequalityProgress
