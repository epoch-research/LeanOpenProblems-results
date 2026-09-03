import Submission.DivisorEnergy

/-! An elementary fourth moment for the divisor function, for controlling
sparse prime-power-factor errors. This is not a prime-pair lower bound. -/
namespace Erdos972DivisorFourthMoment

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta
open Erdos972DivisorEnergy
set_option maxHeartbeats 1000000

lemma zeta_convolution_power_multiplicative (k : ℕ) :
    IsMultiplicative ((ζ : ArithmeticFunction ℝ)^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (isMultiplicative_one (R := ℝ))
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isMultiplicative_zeta.natCast

lemma zeta_convolution_power_prime_pow {p : ℕ} (hp : p.Prime) (k e : ℕ) :
    ((ζ : ArithmeticFunction ℝ)^(k+1)) (p^e) = ((e+k).choose k : ℝ) := by
  induction k generalizing e with
  | zero => simp [natCoe_apply, zeta_apply_ne (pow_ne_zero _ hp.ne_zero)]
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun d b => ((ζ : ArithmeticFunction ℝ)^(k+1)) d *
        (ζ : ArithmeticFunction ℝ) b), Nat.sum_divisors_prime_pow hp]
    have he : (∑ i ∈ range (e+1), ((ζ : ArithmeticFunction ℝ)^(k+1)) (p^i) *
        (ζ : ArithmeticFunction ℝ) (p^e / p^i)) =
        ∑ i ∈ range (e+1), ((i+k).choose k : ℝ) := by
      apply sum_congr rfl
      intro i hi
      have hie : i ≤ e := by simpa only [mem_range, Nat.lt_succ_iff] using hi
      rw [ih, Nat.pow_div hie hp.pos]
      simp [natCoe_apply, zeta_apply_ne (pow_ne_zero _ hp.ne_zero)]
    rw [he, ← Nat.cast_sum, Nat.sum_range_add_choose]
    congr 1

lemma fourth_power_le_choose (e : ℕ) : (e+1)^4 ≤ (e+15).choose 15 := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    have hstep : (e+2)^4 ≤ (e+16)*(e+1)^3 := by
      nlinarith only [Nat.zero_le (e^3), Nat.zero_le (e^2), Nat.zero_le e]
    have hmul := Nat.mul_le_mul_right (e+1) hstep
    have hih := Nat.mul_le_mul_right (e+16) ih
    have hc := Nat.choose_mul_succ_eq (e+15) 15
    have hsub : e+15+1-15 = e+1 := by omega
    rw [hsub] at hc
    have hbound : (e+2)^4*(e+1) ≤ (e+16).choose 15*(e+1) := by
      nlinarith only [hmul, hih, hc]
    have hh := Nat.le_of_mul_le_mul_right hbound (Nat.succ_pos e)
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hh

lemma card_divisors_fourth_le_zeta_sixteen (n : ℕ) :
    (n.divisors.card : ℝ)^4 ≤ ((ζ : ArithmeticFunction ℝ)^16) n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hτ : IsMultiplicative ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) :=
    isMultiplicative_sigma.natCast
  rw [← sigma_zero_apply]
  change (((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) n)^4 ≤ _
  rw [hτ.multiplicative_factorization _ hn,
    (zeta_convolution_power_multiplicative 16).multiplicative_factorization _ hn]
  unfold Finsupp.prod
  rw [← prod_pow]
  apply prod_le_prod (fun _ _ => by positivity)
  intro p hp
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors (by simpa only [n.support_factorization] using hp)
  dsimp only
  rw [natCoe_apply, sigma_zero_apply_prime_pow hpP,
    show (16 : ℕ) = 15+1 from rfl, zeta_convolution_power_prime_pow hpP]
  exact_mod_cast fourth_power_le_choose (n.factorization p)

theorem sum_card_divisors_fourth_le_log (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ)^4) ≤
      (N : ℝ)*(1+Real.log N)^15 := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ((ζ : ArithmeticFunction ℝ)^16) n :=
      sum_le_sum fun n _ => card_divisors_fourth_le_zeta_sixteen n
    _ ≤ (N : ℝ)*(harmonic N : ℝ)^15 := sum_zeta_pow_le 15 N
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (harmonic_real_nonneg N) (harmonic_le_one_add_log N) 15)
      (Nat.cast_nonneg _)

#print axioms zeta_convolution_power_prime_pow
#print axioms card_divisors_fourth_le_zeta_sixteen
#print axioms sum_card_divisors_fourth_le_log

end Erdos972DivisorFourthMoment
