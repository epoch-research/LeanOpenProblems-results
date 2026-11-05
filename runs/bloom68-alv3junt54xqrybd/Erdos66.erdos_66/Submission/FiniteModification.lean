import Submission.FiniteCertificates

/-!
# Finite modifications of ordered representation counts

Changing finitely many memberships changes `sumRep` by a uniformly bounded amount.
After division by `Real.log n`, this error tends to zero.  Thus finite modifications
preserve any real limit, including zero.  All existence consequences below are
conditional on a hypothetical set with the stated limit; none asserts a witness.
This module does not import the conjecture specification.  The final finite
lower-triangular Toeplitz formula is an exact convolution encoding only, not a
linear-programming duality or feasibility assertion.
-/

open Filter AdditiveCombinatorics
open scoped Topology
set_option autoImplicit false
set_option linter.style.namespace false
set_option linter.style.stubs false
set_option linter.style.openClassical false

namespace Erdos66.Compactness

/-- The reciprocal logarithm tends to zero along the natural numbers.  The values
at `0` and `1` use Lean's total logarithm and division conventions. -/
lemma tendsto_one_div_log_nat :
    Tendsto (fun n : ℕ => (1 : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa only [one_div] using
    (tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)))

/-- Any fixed real multiple of the reciprocal logarithm tends to zero. -/
lemma tendsto_const_div_log_nat (K : ℝ) :
    Tendsto (fun n : ℕ => K / Real.log n) atTop (𝓝 0) := by
  simpa only [mul_zero, mul_one_div] using
    (tendsto_const_nhds (x := K)).mul tendsto_one_div_log_nat

/-- The existing ordered-pair bound, normalized by the nonnegative logarithm.
This bound holds even at the two zero-logarithm indices. -/
lemma abs_sumRep_ratio_sub_le_of_agree_off_finset {A B : Set ℕ} (D : Finset ℕ)
    (h : ∀ i, i ∉ D → (i ∈ A ↔ i ∈ B)) (n : ℕ) :
    |(sumRep A n : ℝ) / Real.log n - (sumRep B n : ℝ) / Real.log n| ≤
      (2 * (D.card : ℝ)) / Real.log n := by
  rw [← sub_div, abs_div, abs_of_nonneg (Real.log_natCast_nonneg n)]
  exact div_le_div_of_nonneg_right
    (abs_sumRep_sub_le_of_agree_off_finset D h n) (Real.log_natCast_nonneg n)

/-- A finite membership change contributes a vanishing normalized error. -/
lemma sumRep_ratio_sub_tendsto_zero_of_agree_off_finset {A B : Set ℕ} (D : Finset ℕ)
    (h : ∀ i, i ∉ D → (i ∈ A ↔ i ∈ B)) :
    Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n -
      (sumRep B n : ℝ) / Real.log n) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_) (tendsto_const_div_log_nat (2 * (D.card : ℝ)))
  simpa only [Real.norm_eq_abs] using abs_sumRep_ratio_sub_le_of_agree_off_finset D h n

/-- Finite symmetric difference contributes a vanishing normalized error. -/
lemma sumRep_ratio_sub_tendsto_zero_of_finite_symmDiff {A B : Set ℕ}
    (hD : (symmDiff A B).Finite) :
    Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n -
      (sumRep B n : ℝ) / Real.log n) atTop (𝓝 0) := by
  apply sumRep_ratio_sub_tendsto_zero_of_agree_off_finset hD.toFinset
  intro i hi
  have hi' : i ∉ symmDiff A B := fun hmem => hi (hD.mem_toFinset.mpr hmem)
  rw [Set.mem_symmDiff] at hi'
  tauto

/-- Agreement outside a finite set preserves convergence to the same arbitrary
real `c`; no nonzero or positivity hypothesis on `c` is needed. -/
theorem tendsto_sumRep_ratio_iff_of_agree_off_finset {A B : Set ℕ} (D : Finset ℕ)
    (h : ∀ i, i ∉ D → (i ∈ A ↔ i ∈ B)) (c : ℝ) :
    Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) ↔
      Tendsto (fun n : ℕ => (sumRep B n : ℝ) / Real.log n) atTop (𝓝 c) := by
  have hd := sumRep_ratio_sub_tendsto_zero_of_agree_off_finset D h
  constructor
  · intro hA
    simpa only [sub_zero, sub_sub_cancel] using hA.sub hd
  · intro hB
    simpa only [zero_add, sub_add_cancel] using hd.add hB

/-- Finite symmetric difference preserves convergence of the ordered
representation count divided by `log n`, with exactly the same real limit. -/
theorem tendsto_sumRep_ratio_iff_of_finite_symmDiff {A B : Set ℕ}
    (hD : (symmDiff A B).Finite) (c : ℝ) :
    Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) ↔
      Tendsto (fun n : ℕ => (sumRep B n : ℝ) / Real.log n) atTop (𝓝 c) := by
  have hd := sumRep_ratio_sub_tendsto_zero_of_finite_symmDiff hD
  constructor
  · intro hA
    simpa only [sub_zero, sub_sub_cancel] using hA.sub hd
  · intro hB
    simpa only [zero_add, sub_add_cancel] using hd.add hB

/-- Replace memberships from `0` through `M` by the prescribed pattern `P`,
leaving the tail of `A` unchanged. -/
def graftPrefix (A P : Set ℕ) (M : ℕ) : Set ℕ :=
  {i | (i ≤ M ∧ i ∈ P) ∨ (M < i ∧ i ∈ A)}

@[simp] lemma mem_graftPrefix_of_le {A P : Set ℕ} {M i : ℕ} (hi : i ≤ M) :
    i ∈ graftPrefix A P M ↔ i ∈ P := by
  simp [graftPrefix, hi, not_lt.mpr hi]

@[simp] lemma mem_graftPrefix_of_gt {A P : Set ℕ} {M i : ℕ} (hi : M < i) :
    i ∈ graftPrefix A P M ↔ i ∈ A := by
  simp [graftPrefix, hi, not_le.mpr hi]

/-- The graft changes memberships only inside the specified prefix. -/
lemma symmDiff_graftPrefix_subset_range (A P : Set ℕ) (M : ℕ) :
    symmDiff A (graftPrefix A P M) ⊆ (Finset.range (M + 1) : Set ℕ) := by
  intro i hi
  by_contra hnot
  have hgt : M < i := by
    simpa only [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff, not_le] using hnot
  have hagree := mem_graftPrefix_of_gt (A := A) (P := P) hgt
  rw [Set.mem_symmDiff] at hi
  tauto

lemma finite_symmDiff_graftPrefix (A P : Set ℕ) (M : ℕ) :
    (symmDiff A (graftPrefix A P M)).Finite :=
  (Finset.finite_toSet _).subset (symmDiff_graftPrefix_subset_range A P M)

/-- The graft has the same limit as `A`, for any real `c`. -/
theorem tendsto_sumRep_ratio_graftPrefix_iff (A P : Set ℕ) (M : ℕ) (c : ℝ) :
    Tendsto (fun n : ℕ => (sumRep (graftPrefix A P M) n : ℝ) / Real.log n)
      atTop (𝓝 c) ↔
      Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) :=
  (tendsto_sumRep_ratio_iff_of_finite_symmDiff (finite_symmDiff_graftPrefix A P M) c).symm

/-- Every prescribed finite prefix can be grafted onto a hypothetical limiting
set, without changing its tail or its real limit. -/
theorem exists_same_limit_with_prescribed_prefix {A : Set ℕ} {c : ℝ}
    (hA : Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c))
    (P : Set ℕ) (M : ℕ) :
    ∃ B : Set ℕ, (∀ i ≤ M, i ∈ B ↔ i ∈ P) ∧
      (∀ i, M < i → (i ∈ B ↔ i ∈ A)) ∧
      Tendsto (fun n : ℕ => (sumRep B n : ℝ) / Real.log n) atTop (𝓝 c) := by
  refine ⟨graftPrefix A P M, ?_, ?_,
    (tendsto_sumRep_ratio_graftPrefix_iff A P M c).mpr hA⟩
  · intro i hi
    exact mem_graftPrefix_of_le hi
  · intro i hi
    exact mem_graftPrefix_of_gt hi

/-- Prescribing a finite prefix neither proves nor obstructs the nonzero-limit
existence question.  The construction preserves the same `c`. -/
theorem nonzero_limit_iff_prescribed_prefix (P : Set ℕ) (M : ℕ) :
    (∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) ↔
      ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧ (∀ i ≤ M, i ∈ A ↔ i ∈ P) ∧
        Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  constructor
  · rintro ⟨A, c, hc, hA⟩
    obtain ⟨B, hprefix, _, hB⟩ := exists_same_limit_with_prescribed_prefix hA P M
    exact ⟨B, c, hc, hprefix, hB⟩
  · rintro ⟨A, c, hc, _, hA⟩
    exact ⟨A, c, hc, hA⟩

/-- A hypothetical nonzero-limit witness may be required to contain `0`. -/
theorem nonzero_limit_iff_contains_zero :
    (∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) ↔
      ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧ 0 ∈ A ∧
        Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  simpa using (nonzero_limit_iff_prescribed_prefix (Set.univ : Set ℕ) 0)

/-- A hypothetical nonzero-limit witness may instead be required to omit `0`. -/
theorem nonzero_limit_iff_omits_zero :
    (∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) ↔
      ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧ 0 ∉ A ∧
        Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  simpa using (nonzero_limit_iff_prescribed_prefix (∅ : Set ℕ) 0)

open scoped Classical in
/-- An exact finite sum formula for the ordered representation count. -/
lemma sumRep_eq_sum_range_boole (A : Set ℕ) (n : ℕ) :
    (sumRep A n : ℝ) =
      ∑ i ∈ Finset.range (n + 1), if i ∈ A ∧ n - i ∈ A then (1 : ℝ) else 0 := by
  classical
  rw [sumRep_def, ← Finset.sum_boole]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _

/-- The zero-one membership vector on the finite prefix `0, ..., M`. -/
noncomputable def prefixVector (A : Set ℕ) (M : ℕ) : Fin (M + 1) → ℝ := by
  classical
  exact fun i => if (i : ℕ) ∈ A then 1 else 0

/-- The lower-triangular Toeplitz convolution matrix of the prefix of `A`.
Its entry at row `i`, column `j` is `1_A(i - j)` when `j ≤ i`, and zero otherwise.
The matrix coefficients themselves depend on `A`. -/
noncomputable def prefixToeplitz (A : Set ℕ) (M : ℕ) :
    Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ := by
  classical
  exact fun i j => if (j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) - (j : ℕ) ∈ A then 1 else 0

open scoped Matrix in
/-- Multiplying the finite Toeplitz matrix by its membership vector recovers
exactly the ordered representation counts through `M`.  This is only an exact
finite convolution identity, with no positivity, feasibility, or duality claim. -/
theorem prefixToeplitz_mulVec (A : Set ℕ) (M : ℕ) (n : Fin (M + 1)) :
    (prefixToeplitz A M *ᵥ prefixVector A M) n = (sumRep A (n : ℕ) : ℝ) := by
  classical
  have hterm (i : ℕ) :
      (if i ≤ (n : ℕ) ∧ (n : ℕ) - i ∈ A then (1 : ℝ) else 0) *
        (if i ∈ A then 1 else 0) =
      if i ≤ (n : ℕ) then (if i ∈ A ∧ (n : ℕ) - i ∈ A then 1 else 0) else 0 := by
    by_cases hi : i ≤ (n : ℕ) <;> by_cases hA : i ∈ A <;>
      by_cases hsub : (n : ℕ) - i ∈ A <;> simp [hi, hA, hsub]
  have hrange : (Finset.range (M + 1)).filter (fun i => i ≤ (n : ℕ)) =
      Finset.range ((n : ℕ) + 1) := by
    ext i
    have hn := n.isLt
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  change (∑ i : Fin (M + 1),
    (if (i : ℕ) ≤ (n : ℕ) ∧ (n : ℕ) - (i : ℕ) ∈ A then (1 : ℝ) else 0) *
      (if (i : ℕ) ∈ A then 1 else 0)) = _
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if i ≤ (n : ℕ) then
      (if i ∈ A ∧ (n : ℕ) - i ∈ A then (1 : ℝ) else 0) else 0) (M + 1),
    ← Finset.sum_filter, hrange]
  exact (sumRep_eq_sum_range_boole A (n : ℕ)).symm

end Erdos66.Compactness
