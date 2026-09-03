import Submission.CofactorConductorSplit

/-!
# Summing the small-conductor cofactor error over all moduli

The divisibility constraint on a conductor is retained in the summation.
Consequently the bound has only a subpower dependence on the modulus
cutoff, instead of paying for every modulus separately.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma totient_ratio_le_two_pow_primeFactors (d : ℕ) (hd : 0 < d) :
    (d : ℝ)/(d.totient : ℝ) ≤ (2 : ℝ)^d.primeFactors.card := by
  rw [Sieve.totient_ratio_eq_prime_product d hd,← prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_nonneg (by positivity) (by linarith)
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    apply (div_le_iff₀ (by linarith : (0 : ℝ)<(p : ℝ)-1)).mpr
    linarith only [hp2]

lemma two_pow_primeFactors_div_totient_le (d : ℕ) (hd : 0 < d) :
    (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ (4 : ℝ)^d.primeFactors.card/(d : ℝ) := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  apply (le_div_iff₀ hdR).mpr
  have hh := mul_le_mul_of_nonneg_left (totient_ratio_le_two_pow_primeFactors d hd)
    (show (0 : ℝ) ≤ 2^d.primeFactors.card by positivity)
  convert hh using 1
  · ring
  · rw [← mul_pow]; norm_num

lemma exists_uniform_two_pow_primeFactors_div_totient (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q d : ℕ, 0 < d → d ≤ Q →
      (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ) ≤ C*(Q : ℝ)^ε/(d : ℝ) := by
  obtain ⟨C,hC,HC⟩ := Sieve.exists_card_pow_le_const_product_rpow 4 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro Q d hd hdQ
  apply (two_pow_primeFactors_div_totient_le d hd).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  apply (HC d.primeFactors (fun p hp => Nat.pos_of_mem_primeFactors hp)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hε.le
  exact_mod_cast (Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d)).trans hdQ

lemma smallConductorCofactorWeight_le_divisor_sum (d R : ℕ) :
    smallConductorCofactorWeight d R ≤
      ∑ c ∈ Icc 1 R, if c ∣ d then (c : ℝ)*(Real.sqrt c*(1+Real.log c)) else 0 := by
  rw [← sum_filter]
  apply sum_le_sum_of_subset_of_nonneg
  · intro c hc
    obtain ⟨hcD,hcR⟩ := mem_filter.mp hc
    have hcdiv := (mem_erase.mp hcD).2
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hcdiv,hcR⟩,
      Nat.dvd_of_mem_divisors hcdiv⟩
  · intro c hc hnot
    exact mul_nonneg (Nat.cast_nonneg c)
      (mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_natCast_nonneg c]))

lemma smallConductorCofactorWeight_harmonic_mean (Q R : ℕ) :
    (∑ d ∈ Icc 1 Q, smallConductorCofactorWeight d R/(d : ℝ)) ≤
      (harmonic Q : ℝ)*(R : ℝ)*(Real.sqrt R*(1+Real.log R)) := by
  let H : ℕ → ℝ := fun c => Real.sqrt c*(1+Real.log c)
  have hH : ∀ c, 0 ≤ H c := fun c =>
    mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.log_natCast_nonneg c])
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, (∑ c ∈ Icc 1 R, if c ∣ d then (c : ℝ)*H c else 0)/(d : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact div_le_div_of_nonneg_right (smallConductorCofactorWeight_le_divisor_sum d R)
        (Nat.cast_nonneg d)
    _ = ∑ c ∈ Icc 1 R, (c : ℝ)*H c*(∑ d ∈ Icc 1 Q with c ∣ d, (d : ℝ)⁻¹) := by
      simp only [sum_div]
      rw [sum_comm]
      apply sum_congr rfl
      intro c hc
      rw [sum_filter,mul_sum]
      apply sum_congr rfl
      intro d hd
      split_ifs <;> simp [div_eq_mul_inv]
    _ ≤ ∑ c ∈ Icc 1 R, (c : ℝ)*H c*((c : ℝ)⁻¹*(harmonic Q : ℝ)) := by
      apply sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left
        (Sieve.sum_inv_multiples_le_harmonic Q c (mem_Icc.mp hc).1)
        (mul_nonneg (Nat.cast_nonneg c) (hH c))
    _ = (harmonic Q : ℝ)*∑ c ∈ Icc 1 R, H c := by
      rw [mul_sum]
      apply sum_congr rfl
      intro c hc
      have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hc).1)
      field_simp
    _ ≤ (harmonic Q : ℝ)*∑ _c ∈ Icc 1 R, H R := by
      apply mul_le_mul_of_nonneg_left _ (by
        rw [harmonic_eq_sum_Icc]
        push_cast
        exact sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)))
      apply sum_le_sum
      intro c hc
      have hcR : (c : ℝ) ≤ R := by exact_mod_cast (mem_Icc.mp hc).2
      exact mul_le_mul (Real.sqrt_le_sqrt hcR)
        (add_le_add le_rfl (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hc).1) hcR))
        (by linarith [Real.log_natCast_nonneg c]) (Real.sqrt_nonneg _)
    _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]; dsimp [H]; ring

/-- All positive moduli up to Q are allowed; there is no roughness condition
on their prime factors. The constant depends only on epsilon. -/
theorem exists_small_conductor_mean_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q R : ℕ,
      (∑ d ∈ Icc 1 Q, (2 : ℝ)^d.primeFactors.card/(d.totient : ℝ)*
        smallConductorCofactorWeight d R) ≤
          C*(Q : ℝ)^ε*(harmonic Q : ℝ)*(R : ℝ)*(Real.sqrt R*(1+Real.log R)) := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_two_pow_primeFactors_div_totient ε hε
  refine ⟨C,hC,?_⟩
  intro Q R
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, C*(Q : ℝ)^ε/(d : ℝ)*smallConductorCofactorWeight d R := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (HC Q d (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)
        (smallConductorCofactorWeight_nonneg d R)
    _ = C*(Q : ℝ)^ε*∑ d ∈ Icc 1 Q, smallConductorCofactorWeight d R/(d : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (smallConductorCofactorWeight_harmonic_mean Q R)
        (show 0 ≤ C*(Q : ℝ)^ε by positivity)
      convert hh using 1; ring

end Erdos821.AnalyticSieve
