import Submission.SelbergDefect

/-! The exact Dirichlet-form mean for lower Selberg weights with arbitrary
orthogonal coefficients. No positivity at quadratic interval length is asserted. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def linearKernel (q : ι → ℝ) (c : Finset ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∑ Q : Finset ι, c Q * basis q Q ω

lemma sum_all_split (i : ι) (f : Finset ι → ℝ) :
    (∑ Q : Finset ι, f Q) =
      ∑ Q ∈ (univ.erase i).powerset, (f Q + f (insert i Q)) := by
  conv_lhs => rw [← powerset_univ, ← insert_erase (mem_univ i)]
  rw [sum_powerset_insert (notMem_erase i univ), sum_add_distrib]

lemma not_mem_of_erase_powerset {i : ι} {Q : Finset ι}
    (hQ : Q ∈ (univ.erase i).powerset) : i ∉ Q := by
  intro hi
  exact notMem_erase i univ (mem_powerset.mp hQ hi)

lemma average_hit_basis_mul (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (Q R : Finset ι) (i : ι) (hiQ : i ∉ Q) (hiR : i ∉ R) :
    average q (fun ω => hitCoordinate i ω * (basis q Q ω * basis q R ω)) =
      q i * (if Q = R then variance q Q else 0) := by
  have heq : (fun ω => hitCoordinate i ω * (basis q Q ω * basis q R ω)) =
      (fun ω => q i * (basis q Q ω * basis q R ω - basis q (insert i Q) ω * basis q R ω)) := by
    funext ω
    rw [← mul_assoc, hitCoordinate_mul_basis_of_not_mem q Q i (hq i) hiQ]
    ring
  rw [heq, average_mul_const, average_sub, average_basis_mul q hq, average_basis_mul q hq]
  have hne : insert i Q ≠ R := by intro he; exact hiR (he ▸ mem_insert_self i Q)
  simp only [hne, if_false, sub_zero]

lemma average_hit_square_sum (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (D : Finset (Finset ι)) (c : Finset ι → ℝ) (i : ι) (hD : ∀ Q ∈ D, i ∉ Q) :
    average q (fun ω => hitCoordinate i ω * (∑ Q ∈ D, c Q * basis q Q ω) ^ 2) =
      q i * ∑ Q ∈ D, c Q ^ 2 * variance q Q := by
  have heq : (fun ω => hitCoordinate i ω * (∑ Q ∈ D, c Q * basis q Q ω) ^ 2) =
      fun ω => ∑ Q ∈ D, ∑ R ∈ D,
        (c Q * c R) * (hitCoordinate i ω * (basis q Q ω * basis q R ω)) := by
    funext ω
    rw [pow_two, sum_mul_sum, mul_sum]
    apply sum_congr rfl
    intro Q hQ
    rw [mul_sum]
    apply sum_congr rfl
    intro R hR
    ring
  rw [heq, average_sum, mul_sum]
  apply sum_congr rfl
  intro Q hQ
  rw [average_sum]
  have hterm (R : Finset ι) (hR : R ∈ D) :
      average q (fun ω => (c Q * c R) * (hitCoordinate i ω * (basis q Q ω * basis q R ω))) =
        if Q = R then q i * (c Q ^ 2 * variance q Q) else 0 := by
    rw [average_mul_const, average_hit_basis_mul q hq Q R i (hD Q hQ) (hD R hR)]
    split_ifs with h
    · rw [← h]; ring
    · ring
  rw [sum_congr rfl hterm]
  simp [hQ]

lemma linearKernel_at_hit (q : ι → ℝ) (hq : ∀ i, q i ≠ 0) (c : Finset ι → ℝ)
    (i : ι) (ω : ι → Bool) (hω : ω i = true) :
    linearKernel q c ω = ∑ Q ∈ (univ.erase i).powerset,
      (c Q - ((1 - q i) / q i) * c (insert i Q)) * basis q Q ω := by
  rw [linearKernel, sum_all_split i]
  apply sum_congr rfl
  intro Q hQ
  rw [basis_insert q Q i (not_mem_of_erase_powerset hQ)]
  simp only [contrast, hω, if_true]
  field_simp [hq i]
  <;> ring

/-- Every coordinate contributes an exact squared difference of adjacent orthogonal coefficients. -/
theorem linearKernel_hit_average (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (c : Finset ι → ℝ) (i : ι) :
    average q (fun ω => hitCoordinate i ω * linearKernel q c ω ^ 2) =
      q i * ∑ Q ∈ (univ.erase i).powerset,
        (c Q - ((1 - q i) / q i) * c (insert i Q)) ^ 2 * variance q Q := by
  have heq : (fun ω => hitCoordinate i ω * linearKernel q c ω ^ 2) =
      (fun ω => hitCoordinate i ω * (∑ Q ∈ (univ.erase i).powerset,
        (c Q - ((1 - q i) / q i) * c (insert i Q)) * basis q Q ω) ^ 2) := by
    funext ω
    cases hω : ω i with
    | false => simp [hitCoordinate, hω]
    | true => rw [linearKernel_at_hit q hq c i ω hω]
  rw [heq]
  exact average_hit_square_sum q hq _ _ i (fun Q hQ => not_mem_of_erase_powerset hQ)

noncomputable def kernelEnergy (q : ι → ℝ) (c : Finset ι → ℝ) : ℝ :=
  (∑ Q : Finset ι, c Q ^ 2 * variance q Q) -
    ∑ i, q i * ∑ Q ∈ (univ.erase i).powerset,
      (c Q - ((1 - q i) / q i) * c (insert i Q)) ^ 2 * variance q Q

/-- Exact mean of an arbitrary squared kernel penalized by the number of hits. -/
theorem lowerKernel_average (q : ι → ℝ) (hq : ∀ i, q i ≠ 0) (c : Finset ι → ℝ) :
    average q (fun ω => (1 - ∑ i, hitCoordinate i ω) * linearKernel q c ω ^ 2) =
      kernelEnergy q c := by
  have heq : (fun ω => (1 - ∑ i, hitCoordinate i ω) * linearKernel q c ω ^ 2) =
      fun ω => linearKernel q c ω ^ 2 - ∑ i, hitCoordinate i ω * linearKernel q c ω ^ 2 := by
    funext ω
    rw [← sum_mul]
    ring
  rw [heq, average_sub, average_sum]
  simp_rw [linearKernel_hit_average q hq]
  rw [kernelEnergy]
  congr 1
  exact average_square_sum q hq univ c

lemma variance_insert (q : ι → ℝ) (Q : Finset ι) (i : ι) (hi : i ∉ Q) :
    variance q (insert i Q) = ((1 - q i) / q i) * variance q Q := by
  simp only [variance, prod_insert hi]

/-- In reciprocal-variance coordinates, the energy is a weighted discrete Dirichlet form. -/
theorem kernelEnergy_weighted (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (f : Finset ι → ℝ) :
    kernelEnergy q (fun Q => weight q Q * f Q) =
      (∑ Q : Finset ι, weight q Q * f Q ^ 2) -
        ∑ i, q i * ∑ Q ∈ (univ.erase i).powerset,
          weight q Q * (f Q - f (insert i Q)) ^ 2 := by
  rw [kernelEnergy]
  congr 1
  · apply sum_congr rfl
    intro Q hQ
    rw [weight_eq_inverse_variance]
    have hv := (variance_pos q hq Q).ne'
    field_simp
  · apply sum_congr rfl
    intro i hi
    congr 1
    apply sum_congr rfl
    intro Q hQ
    rw [weight_insert q Q i (not_mem_of_erase_powerset hQ), weight_eq_inverse_variance]
    have hv := (variance_pos q hq Q).ne'
    have hq0 := (hq i).1.ne'
    have hq1 := (sub_pos.mpr (hq i).2).ne'
    field_simp
    <;> ring

#print axioms lowerKernel_average
#print axioms kernelEnergy_weighted
end Erdos970.FiniteSelberg
