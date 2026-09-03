import Submission.SelbergSoftEnergy

/-! A finite support-mass upper bound for a common lower Selberg kernel.
The coefficient function need not be radial. The arithmetic size of the
support-mass factor is not estimated here. This is not a Jacobsthal disproof. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma probability_nonneg (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (ω : ι → Bool) : 0 ≤ probability q ω := by
  apply prod_nonneg
  intro i hi
  cases hb : ω i <;> simp only [hb, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr (hq i).2
  · exact (hq i).1

lemma hitCoordinate_nonneg (i : ι) (ω : ι → Bool) : 0 ≤ hitCoordinate i ω := by
  unfold hitCoordinate
  cases ω i <;> norm_num

/-- The lower polynomial is positive only at the empty hit pattern. -/
theorem kernelEnergy_le_empty_atom (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (c : Finset ι → ℝ) :
    kernelEnergy q c ≤ (∏ i, (1 - q i)) * (∑ Q : Finset ι, c Q) ^ 2 := by
  classical
  have hpoint (ω : ι → Bool) :
      (1 - ∑ i, hitCoordinate i ω) * linearKernel q c ω ^ 2 ≤
      if ω = (fun _ => false) then (∑ Q : Finset ι, c Q) ^ 2 else 0 := by
    by_cases hω : ω = (fun _ => false)
    · subst ω
      simp [linearKernel, basis_at_empty, hitCoordinate]
    · rw [if_neg hω]
      have hex : ∃ i, ω i = true := by
        by_contra h
        push_neg at h
        apply hω
        funext i
        cases hi : ω i with
        | false => rfl
        | true => exact False.elim (h i hi)
      obtain ⟨i, hi⟩ := hex
      have hs := single_le_sum (s := (univ : Finset ι))
        (f := fun j => hitCoordinate j ω) (fun j _ => hitCoordinate_nonneg j ω) (mem_univ i)
      have hi1 : hitCoordinate i ω = 1 := by simp [hitCoordinate, hi]
      dsimp only at hs
      rw [hi1] at hs
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  rw [← lowerKernel_average q (fun i => (hq i).1.ne')]
  have hm := sum_le_sum (fun ω (_ : ω ∈ (univ : Finset (ι → Bool))) =>
    mul_le_mul_of_nonneg_left (hpoint ω) (probability_nonneg q
      (fun i => ⟨(hq i).1.le, (hq i).2.le⟩) ω))
  change average q (fun ω => (1 - ∑ i, hitCoordinate i ω) * linearKernel q c ω ^ 2) ≤ _ at hm
  apply hm.trans_eq
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  simp only [probability, Bool.false_eq_true, ↓reduceIte]

/-- Orthogonal support uncertainty: small support mass limits the positive
mean, even if coefficients are not functions of the product of their primes. -/
theorem kernelEnergy_weighted_support_upper (q : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (D : Finset (Finset ι))
    (f : Finset ι → ℝ) (hf : ∀ Q, Q ∉ D → f Q = 0) :
    kernelEnergy q (fun Q => weight q Q * f Q) ≤
      ((∏ i, (1 - q i)) * (∑ Q ∈ D, weight q Q)) *
        ∑ Q : Finset ι, weight q Q * f Q ^ 2 := by
  classical
  have hlin : (∑ Q ∈ D, weight q Q * f Q) = ∑ Q : Finset ι, weight q Q * f Q := by
    apply sum_subset (subset_univ D)
    intro Q hQ hQD
    simp only [hf Q hQD, mul_zero]
  have hsq : (∑ Q ∈ D, weight q Q * f Q ^ 2) =
      ∑ Q : Finset ι, weight q Q * f Q ^ 2 := by
    apply sum_subset (subset_univ D)
    intro Q hQ hQD
    simp only [hf Q hQD, zero_pow (by omega : 2 ≠ 0), mul_zero]
  have hcs : (∑ Q ∈ D, weight q Q * f Q) ^ 2 ≤
      (∑ Q ∈ D, weight q Q) * ∑ Q ∈ D, weight q Q * f Q ^ 2 := by
    apply sum_sq_le_sum_mul_sum_of_sq_eq_mul
      (s := D) (r := fun Q => weight q Q * f Q)
      (f := weight q) (g := fun Q => weight q Q * f Q ^ 2)
    · intro Q hQ
      exact (weight_pos q hq Q).le
    · intro Q hQ
      exact mul_nonneg (weight_pos q hq Q).le (sq_nonneg _)
    · intro Q hQ
      ring
  rw [hlin, hsq] at hcs
  have hd : 0 ≤ ∏ i, (1 - q i) := prod_nonneg (fun i _ => sub_nonneg.mpr (hq i).2.le)
  have hh := (kernelEnergy_le_empty_atom q hq (fun Q => weight q Q * f Q)).trans
    (mul_le_mul_of_nonneg_left hcs hd)
  convert hh using 1 <;> ring

/-- A scalar tail penalty at least the normalized core support mass precludes
positive common-kernel energy. The support-mass inequality is an explicit
hypothesis, not an unproved asymptotic estimate. -/
theorem common_tail_energy_nonpos_of_mass (q : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (D : Finset (Finset ι))
    (f : Finset ι → ℝ) (hf : ∀ Q, Q ∉ D → f Q = 0)
    (T : ℝ) (hT : (∏ i, (1 - q i)) * (∑ Q ∈ D, weight q Q) ≤ T) :
    kernelEnergy q (fun Q => weight q Q * f Q) -
      T * (∑ Q : Finset ι, weight q Q * f Q ^ 2) ≤ 0 := by
  have hn : 0 ≤ ∑ Q : Finset ι, weight q Q * f Q ^ 2 :=
    sum_nonneg (fun Q _ => mul_nonneg (weight_pos q hq Q).le (sq_nonneg _))
  have hu := kernelEnergy_weighted_support_upper q hq D f hf
  have ht := mul_le_mul_of_nonneg_right hT hn
  linarith

#print axioms kernelEnergy_le_empty_atom
#print axioms kernelEnergy_weighted_support_upper
#print axioms common_tail_energy_nonpos_of_mass
end Erdos970.FiniteSelberg
