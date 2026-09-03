import Submission.EulerMassLogUpper

/-! Exponential-moment control of the omitted part of a Selberg divisor
normalizer. The prime exponential sum is retained explicitly in the generic
bound; no positivity of a first-hit sieve is asserted. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma primeWeight_sum_eq_eulerMass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ Q ∈ P.powerset, primeWeight Q) = eulerMass P := by
  unfold primeWeight eulerMass
  rw [← prod_one_add]
  apply prod_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have hh : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    linarith
  field_simp
  ring

lemma primeWeight_exponential_sum (P : Finset ℕ) (t : ℝ) :
    (∑ Q ∈ P.powerset, primeWeight Q * exp (t * ∑ p ∈ Q, log (p : ℝ))) =
      ∏ p ∈ P, (1 + exp (t * log (p : ℝ)) / ((p : ℝ) - 1)) := by
  simp only [primeWeight, mul_sum, exp_sum, ← prod_mul_distrib, one_div_mul_eq_div]
  rw [prod_one_add]

lemma primeWeight_exponential_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    (∑ Q ∈ P.powerset, primeWeight Q * exp (t * ∑ p ∈ Q, log (p : ℝ))) ≤
      eulerMass P * exp (∑ p ∈ P, (exp (t * log (p : ℝ)) - 1) / p) := by
  rw [primeWeight_exponential_sum, eulerMass, exp_sum, ← prod_mul_distrib]
  apply prod_le_prod
  · intro p hp
    have hpp : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    have hd : 0 < (p : ℝ) - 1 := by linarith
    positivity
  · intro p hp
    have hpp : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hd : 0 < 1 - 1 / (p : ℝ) := by
      have hh := (div_lt_one hp0).mpr hpp
      linarith
    have hid : 1 + exp (t * log (p : ℝ)) / ((p : ℝ) - 1) =
        (1 - 1 / (p : ℝ))⁻¹ * (1 + (exp (t * log (p : ℝ)) - 1) / p) := by
      field_simp [hp0.ne', (sub_pos.mpr hpp).ne']
      <;> ring
    rw [hid]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hd.le)
    simpa only [add_comm] using add_one_le_exp ((exp (t * log (p : ℝ)) - 1) / p)

lemma eulerMass_sub_normalizer_eq_tail (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    eulerMass P - primeNormalizer P N =
      ∑ Q ∈ P.powerset with N < ∏ p ∈ Q, p, primeWeight Q := by
  have hh := sum_filter_add_sum_filter_not P.powerset (fun Q => ∏ p ∈ Q, p ≤ N) primeWeight
  simp only [not_le] at hh
  rw [primeWeight_sum_eq_eulerMass P hP] at hh
  change primeNormalizer P N + _ = eulerMass P at hh
  linarith

/-- Rankin's bound for the normalizer tail, for arbitrary finite prime sets.
The transform is that of independent squarefree prime factors, not of the
interval survivor count. -/
theorem eulerMass_sub_normalizer_rankin (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : 0 ≤ t) :
    eulerMass P - primeNormalizer P N ≤
      eulerMass P * exp ((∑ p ∈ P, (exp (t * log (p : ℝ)) - 1) / p) - t * log (N : ℝ)) := by
  have hlow : exp (t * log (N : ℝ)) * (eulerMass P - primeNormalizer P N) ≤
      ∑ Q ∈ P.powerset, primeWeight Q * exp (t * ∑ p ∈ Q, log (p : ℝ)) := by
    rw [eulerMass_sub_normalizer_eq_tail P hP N, mul_sum]
    apply (sum_le_sum (fun Q hQ => ?_)).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun Q hQ _ =>
        mul_nonneg (primeWeight_nonneg Q (fun p hp => hP p ((mem_powerset.mp hQ) hp))) (exp_pos _).le))
    obtain ⟨hQP, hNQ⟩ := mem_filter.mp hQ
    have hpr : ∀ p ∈ Q, p.Prime := fun p hp => hP p ((mem_powerset.mp hQP) hp)
    have hprod : log ((∏ p ∈ Q, p : ℕ) : ℝ) = ∑ p ∈ Q, log (p : ℝ) := by
      rw [Nat.cast_prod, log_prod]
      intro p hp
      exact_mod_cast (hpr p hp).ne_zero
    have hh := log_le_log (show (0 : ℝ) < N by exact_mod_cast hN)
      (show (N : ℝ) ≤ (∏ p ∈ Q, p : ℕ) by exact_mod_cast hNQ.le)
    rw [hprod] at hh
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hh ht)) (primeWeight_nonneg Q hpr)
  have hh := hlow.trans (primeWeight_exponential_sum_le P hP t)
  have hh' := mul_le_mul_of_nonneg_left hh (exp_pos (-(t * log (N : ℝ)))).le
  have he : exp (-(t * log (N : ℝ))) * exp (t * log (N : ℝ)) = 1 := by
    rw [← exp_add]
    simp
  rw [← mul_assoc, he, one_mul] at hh'
  convert hh' using 1
  rw [exp_sub, exp_neg]
  ring

#print axioms primeWeight_sum_eq_eulerMass
#print axioms primeWeight_exponential_sum_le
#print axioms eulerMass_sub_normalizer_rankin
end Erdos970.FiniteSelberg
