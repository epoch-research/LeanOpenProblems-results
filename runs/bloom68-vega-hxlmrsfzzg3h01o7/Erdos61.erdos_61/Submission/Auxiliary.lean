import FormalConjecturesUtil

/-!
# Standalone reductions for Erdős–Hajnal (Erdős Problem 61)

This file does not import `Submission.Spec` or use either of its admitted declarations.
`Auxiliary.IsErdosHajnalLowerBound` is a verbatim copy of the predicate in that file.
The results below are conditional reductions and logical normalizations, not a proof
or disproof of the Erdős–Hajnal conjecture.
-/

open Filter
open SimpleGraph

namespace Auxiliary

universe u

/-- The exact lower-bound predicate from `Erdos61`, copied to keep this file standalone. -/
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

section ProductReduction

/-- Halving a real exponent and then squaring recovers the original power,
including at the nonnegative base zero. -/
theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) (e : ℝ) :
    (x ^ (e / 2)) ^ (2 : ℕ) = x ^ e := by
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  norm_num

/-- A square bounded by a product of nonnegative numbers is bounded by one factor. -/
theorem le_or_le_of_sq_le_mul {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ (2 : ℕ) ≤ a * b) : x ≤ a ∨ x ≤ b := by
  by_contra! hnot
  have hx : 0 < x := lt_of_le_of_lt ha hnot.1
  have hprod : a * b < x * x :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hnot.1.le hb)
      (mul_lt_mul_of_pos_left hnot.2 hx)
  exact (not_lt_of_ge h) (by simpa only [pow_two] using hprod)

/-- Pointwise graph-theoretic reduction. Positivity of `e` is not needed for this step. -/
theorem homogeneous_bound_of_product_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (e : ℝ) (hproduct : (n : ℝ) ^ e ≤ (G.indepNum : ℝ) * (G.cliqueNum : ℝ)) :
    (n : ℝ) ^ (e / 2) ≤ (G.indepNum : ℝ) ∨
      (n : ℝ) ^ (e / 2) ≤ (G.cliqueNum : ℝ) := by
  apply le_or_le_of_sq_le_mul (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simpa only [rpow_half_sq (Nat.cast_nonneg n) e] using hproduct

/-- An eventual product bound gives the exact lower-bound predicate with exponent `e / 2`.
There is no loss of an additional constant or of any vertices. -/
theorem isErdosHajnalLowerBound_of_product_bound
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α) (e : ℝ)
    (hproduct : ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        (n : ℝ) ^ e ≤ (G.indepNum : ℝ) * (G.cliqueNum : ℝ)) :
    IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ (e / 2)) := by
  filter_upwards [hproduct] with n hn
  intro G hfree
  exact homogeneous_bound_of_product_bound G e (hn G hfree)

/-- A positive exponent in the product bound suffices for the conjecture at a fixed `H`. -/
theorem erdosHajnal_of_product_bound
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α)
    {e : ℝ} (he : 0 < e)
    (hproduct : ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        (n : ℝ) ^ e ≤ (G.indepNum : ℝ) * (G.cliqueNum : ℝ)) :
    ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c) := by
  exact ⟨e / 2, half_pos he, isErdosHajnalLowerBound_of_product_bound H e hproduct⟩

/-- The full conjecture follows *conditionally* if the positive product estimates are proved
for every finite forbidden graph. The hypothesis here remains a substantive open obligation. -/
theorem erdosHajnal_of_product_estimates
    (hproduct : ∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ e > (0 : ℝ), ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
        (¬∃ g : α ↪ Fin n, H = G.comap g) →
          (n : ℝ) ^ e ≤ (G.indepNum : ℝ) * (G.cliqueNum : ℝ)) :
    ∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c) := by
  intro α _ _ H
  obtain ⟨e, he, hbound⟩ := hproduct H
  exact erdosHajnal_of_product_bound H he hbound

end ProductReduction

section Counterexamples

/-- Failure of the exact eventual predicate means counterexamples of arbitrarily large order.
The forbidden graph is fixed, and both the clique and independence bounds fail strictly. -/
theorem not_isErdosHajnalLowerBound_iff
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α) (f : ℕ → ℝ) :
    (¬ IsErdosHajnalLowerBound H f) ↔
      ∀ N : ℕ, ∃ n ≥ N, ∃ G : SimpleGraph (Fin n),
        (¬∃ g : α ↪ Fin n, H = G.comap g) ∧
          (G.indepNum : ℝ) < f n ∧ (G.cliqueNum : ℝ) < f n := by
  classical
  simp only [IsErdosHajnalLowerBound, eventually_atTop, not_exists, not_forall,
    not_or, not_le, exists_prop]

/-- At a fixed `H`, failure for every positive exponent is equivalent to arbitrarily large
counterexamples for each positive exponent. The order may depend on both `c` and `N`. -/
theorem not_exists_pos_lowerBound_iff
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α) :
    (¬ ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)) ↔
      ∀ c > (0 : ℝ), ∀ N : ℕ, ∃ n ≥ N, ∃ G : SimpleGraph (Fin n),
        (¬∃ g : α ↪ Fin n, H = G.comap g) ∧
          (G.indepNum : ℝ) < (n : ℝ) ^ c ∧ (G.cliqueNum : ℝ) < (n : ℝ) ^ c := by
  classical
  simp only [not_exists, not_and, not_isErdosHajnalLowerBound_iff]

/-- Exact negation of the full conjecture (at any fixed universe level): one fixed finite `H`
must have arbitrarily large counterexamples for *every* positive exponent. This is only an
iff, not an assertion that such a graph exists. -/
theorem not_erdosHajnal_iff :
    (¬ ∀ {α : Type u} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
      ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)) ↔
      ∃ (α : Type u) (_ : Fintype α) (_ : DecidableEq α) (H : SimpleGraph α),
        ∀ c > (0 : ℝ), ∀ N : ℕ, ∃ n ≥ N, ∃ G : SimpleGraph (Fin n),
          (¬∃ g : α ↪ Fin n, H = G.comap g) ∧
            (G.indepNum : ℝ) < (n : ℝ) ^ c ∧ (G.cliqueNum : ℝ) < (n : ℝ) ^ c := by
  classical
  simp only [not_forall, not_exists_pos_lowerBound_iff]

end Counterexamples

namespace FiniteMixing

variable {V : Type*}

/-- No two disjoint `q`-element finsets are complete or anticomplete to one another. -/
def NoHomogeneousPair (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
    ¬ ((∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) ∨ (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y))

/-- The empty pair rules out the mixing condition at `q = 0`. -/
theorem NoHomogeneousPair.pos {G : SimpleGraph V} {q : ℕ}
    (hmix : NoHomogeneousPair G q) : 0 < q := by
  by_contra h
  have hq : q = 0 := by omega
  apply hmix ∅ ∅ (by simp) (by simp [hq]) (by simp [hq])
  exact Or.inl (by simp)

/-- The one-sided counting argument, valid for any decidable relation.
If there is no anticomplete disjoint `q`-pair, fewer than `q` candidates can have fewer
than `s` related elements in a disjoint target of size at least `q * s`. -/
theorem card_few_related_lt (R : V → V → Prop) [DecidableRel R]
    {q s : ℕ} (hq : 0 < q)
    (hno : ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
      ¬ (∀ x ∈ X, ∀ y ∈ Y, ¬ R x y))
    (A B : Finset V) (hdisj : Disjoint B A) (hA : q * s ≤ A.card) :
    (B.filter (fun b => (A.filter (R b)).card < s)).card < q := by
  classical
  by_cases hs : s = 0
  · simpa [hs] using hq
  have hspos : 1 ≤ s := by omega
  by_contra! hbad
  obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hbad
  let U : Finset V := C.biUnion (fun b => A.filter (R b))
  have hCsmall : ∀ b ∈ C, (A.filter (R b)).card ≤ s - 1 := by
    intro b hb
    have hsmall := (Finset.mem_filter.mp (hCsub hb)).2
    omega
  have hU : U.card ≤ q * (s - 1) := by
    simpa only [U, hCcard] using
      Finset.card_biUnion_le_card_mul C (fun b => A.filter (R b)) (s - 1) hCsmall
  have hscale : q * (s - 1) + q = q * s := by
    calc
      q * (s - 1) + q = q * ((s - 1) + 1) := by ring
      _ = q * s := by rw [Nat.sub_add_cancel hspos]
  have hleft : q ≤ (A \ U).card := by
    have hcover := Finset.card_le_card_sdiff_add_card (s := A) (t := U)
    omega
  obtain ⟨D, hDsub, hDcard⟩ := Finset.exists_subset_card_eq hleft
  have hCB : C ⊆ B := fun b hb => (Finset.mem_filter.mp (hCsub hb)).1
  have hDA : D ⊆ A := fun a ha => (Finset.mem_sdiff.mp (hDsub ha)).1
  apply hno C D (hdisj.mono hCB hDA) hCcard hDcard
  intro b hb a ha hba
  have haU : a ∈ U :=
    Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨hDA ha, hba⟩⟩
  exact (Finset.mem_sdiff.mp (hDsub ha)).2 haU

/-- Fewer than `q` candidates fail the neighbor requirement for a single target. -/
theorem card_few_neighbors_lt {G : SimpleGraph V} [DecidableRel G.Adj]
    {q s : ℕ} (hmix : NoHomogeneousPair G q)
    (A B : Finset V) (hdisj : Disjoint B A) (hA : q * s ≤ A.card) :
    (B.filter (fun b => (A.filter (G.Adj b)).card < s)).card < q := by
  refine card_few_related_lt G.Adj hmix.pos ?_ A B hdisj hA
  intro X Y hXY hX hY hanti
  exact hmix X Y hXY hX hY (Or.inr hanti)

/-- Fewer than `q` candidates fail the nonneighbor requirement for a single target. -/
theorem card_few_nonneighbors_lt {G : SimpleGraph V} [DecidableRel G.Adj]
    {q s : ℕ} (hmix : NoHomogeneousPair G q)
    (A B : Finset V) (hdisj : Disjoint B A) (hA : q * s ≤ A.card) :
    (B.filter (fun b => (A.filter (fun a => ¬ G.Adj b a)).card < s)).card < q := by
  refine card_few_related_lt (fun x y => ¬ G.Adj x y) hmix.pos ?_ A B hdisj hA
  intro X Y hXY hX hY hanti
  apply hmix X Y hXY hX hY
  exact Or.inl (fun x hx y hy => not_not.mp (hanti x hx y hy))

/-- A finite family of large targets has a simultaneous splitting vertex.
Only disjointness of each target from `B` is required; the targets may overlap one another.
The cases `s = 0` and an empty index finset are included. -/
theorem exists_vertex_splitting {G : SimpleGraph V} [DecidableRel G.Adj]
    {ι : Type*} {q s : ℕ} (hmix : NoHomogeneousPair G q)
    (J : Finset ι) (A : ι → Finset V) (B : Finset V)
    (hdisj : ∀ j ∈ J, Disjoint B (A j))
    (hA : ∀ j ∈ J, q * s ≤ (A j).card)
    (hB : 2 * J.card * (q - 1) + 1 ≤ B.card) :
    ∃ b ∈ B, ∀ j ∈ J,
      s ≤ ((A j).filter (G.Adj b)).card ∧
        s ≤ ((A j).filter (fun a => ¬ G.Adj b a)).card := by
  classical
  let bad : ι → Finset V := fun j =>
    B.filter (fun b => ((A j).filter (G.Adj b)).card < s) ∪
      B.filter (fun b => ((A j).filter (fun a => ¬ G.Adj b a)).card < s)
  have hbad : ∀ j ∈ J, (bad j).card ≤ 2 * (q - 1) := by
    intro j hj
    have hp := card_few_neighbors_lt hmix (A j) B (hdisj j hj) (hA j hj)
    have hn := card_few_nonneighbors_lt hmix (A j) B (hdisj j hj) (hA j hj)
    have hu := Finset.card_union_le
      (B.filter (fun b => ((A j).filter (G.Adj b)).card < s))
      (B.filter (fun b => ((A j).filter (fun a => ¬ G.Adj b a)).card < s))
    dsimp only [bad]
    omega
  have hU : (J.biUnion bad).card ≤ 2 * J.card * (q - 1) := by
    calc
      (J.biUnion bad).card ≤ J.card * (2 * (q - 1)) :=
        Finset.card_biUnion_le_card_mul J bad (2 * (q - 1)) hbad
      _ = 2 * J.card * (q - 1) := by ring
  have hlt : (J.biUnion bad).card < B.card := by omega
  obtain ⟨b, hbB, hbU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨b, hbB, ?_⟩
  intro j hj
  have hbnot : b ∉ bad j := fun hbj => hbU (Finset.mem_biUnion.mpr ⟨j, hj, hbj⟩)
  constructor
  · by_contra! h
    apply hbnot
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hbB, h⟩))
  · by_contra! h
    apply hbnot
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hbB, h⟩))

/-- The `k`-target form: `|A j| ≥ q * s` and `|B| ≥ 2 * k * (q - 1) + 1`
yield a vertex with at least `s` neighbors and at least `s` nonneighbors in every target. -/
theorem exists_vertex_splitting_fin {G : SimpleGraph V} [DecidableRel G.Adj]
    {q s k : ℕ} (hmix : NoHomogeneousPair G q)
    (A : Fin k → Finset V) (B : Finset V)
    (hdisj : ∀ j, Disjoint B (A j))
    (hA : ∀ j, q * s ≤ (A j).card)
    (hB : 2 * k * (q - 1) + 1 ≤ B.card) :
    ∃ b ∈ B, ∀ j : Fin k,
      s ≤ ((A j).filter (G.Adj b)).card ∧
        s ≤ ((A j).filter (fun a => ¬ G.Adj b a)).card := by
  obtain ⟨b, hb, hsplit⟩ := exists_vertex_splitting hmix Finset.univ A B
    (fun j _ => hdisj j) (fun j _ => hA j) (by simpa using hB)
  exact ⟨b, hb, fun j => hsplit j (Finset.mem_univ j)⟩

end FiniteMixing

end Auxiliary

/- Axiom audit

These checks are intentionally kept in the standalone file so that
`lake env lean Submission/Auxiliary.lean` reproduces the audit.
-/

#print axioms Auxiliary.rpow_half_sq
#print axioms Auxiliary.le_or_le_of_sq_le_mul
#print axioms Auxiliary.homogeneous_bound_of_product_bound
#print axioms Auxiliary.isErdosHajnalLowerBound_of_product_bound
#print axioms Auxiliary.erdosHajnal_of_product_bound
#print axioms Auxiliary.erdosHajnal_of_product_estimates
#print axioms Auxiliary.not_isErdosHajnalLowerBound_iff
#print axioms Auxiliary.not_exists_pos_lowerBound_iff
#print axioms Auxiliary.not_erdosHajnal_iff
#print axioms Auxiliary.FiniteMixing.NoHomogeneousPair.pos
#print axioms Auxiliary.FiniteMixing.card_few_related_lt
#print axioms Auxiliary.FiniteMixing.card_few_neighbors_lt
#print axioms Auxiliary.FiniteMixing.card_few_nonneighbors_lt
#print axioms Auxiliary.FiniteMixing.exists_vertex_splitting
#print axioms Auxiliary.FiniteMixing.exists_vertex_splitting_fin
