import Submission.QuadraticSmoothBound

/-! Elementary first-order bounds for the logarithmically weighted prime
harmonic sum, obtained from factorials and Chebyshev's theta bound. -/

namespace Erdos371
namespace FiniteSieve
open Finset

noncomputable def primeLogHarmonic (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, Real.log p / (p : ℝ)

noncomputable def primePowerErrorConstant : ℝ :=
  4 * ∑' n : ℕ, (n : ℝ)^(-3/2 : ℝ)

lemma prime_log_pred_error_bound (p : ℕ) (hp : p.Prime) :
    Real.log p / ((p : ℝ)*((p : ℝ)-1)) ≤ 4*(p : ℝ)^(-3/2 : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpred : (0 : ℝ) < (p : ℝ)-1 := by linarith
  have hlog := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1/2)
  have hpow : 0 ≤ (p : ℝ)^(1/2 : ℝ) := Real.rpow_nonneg hp0.le _
  have hpden : (p : ℝ)^2 ≤ 2*((p : ℝ)*((p : ℝ)-1)) := by nlinarith
  calc
    _ ≤ (2*(p : ℝ)^(1/2 : ℝ))/((p : ℝ)*((p : ℝ)-1)) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hp0.le hpred.le)
      nlinarith
    _ ≤ 4*(p : ℝ)^(1/2 : ℝ)/(p : ℝ)^2 := by
      apply (div_le_div_iff₀ (mul_pos hp0 hpred) (sq_pos_of_pos hp0)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hpden hpow]
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_natCast]
      rw [← Real.rpow_sub hp0]
      norm_num

lemma prime_log_pred_error_sum_bound (N : ℕ) :
    (∑ p ∈ (N+1).primesBelow, Real.log p/((p : ℝ)*((p : ℝ)-1))) ≤
      primePowerErrorConstant := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-3/2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  calc
    _ ≤ ∑ p ∈ (N+1).primesBelow, 4*(p : ℝ)^(-3/2 : ℝ) :=
      sum_le_sum fun p hp => prime_log_pred_error_bound p (Nat.mem_primesBelow.mp hp).2
    _ = 4 * ∑ p ∈ (N+1).primesBelow, (p : ℝ)^(-3/2 : ℝ) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum _ (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)) (by norm_num)

lemma log_factorial_eq_prime_sum (N : ℕ) :
    Real.log N.factorial = ∑ p ∈ (N+1).primesBelow,
      (N.factorial.factorization p : ℝ)*Real.log p := by
  change Real.log N.factorial = smallPrimeLog (N+1) N.factorial
  rw [← smallPrimeLog_factorial]
  have he (n : ℕ) (hn : n ∈ range N) : smallPrimeLog (N+1) (n+1) = Real.log (n+1 : ℕ) := by
    apply smallPrimeLog_eq_log_of_smooth _ _ (by omega)
    exact Nat.maxPrimeFac_le.trans_lt (by have := mem_range.mp hn; omega)
  rw [sum_congr rfl he]
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod,
    Real.log_prod (fun n hn => by positivity)]

lemma primeLogHarmonic_upper (N : ℕ) (hN : 0 < N) :
    primeLogHarmonic N ≤ Real.log N + Real.log 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have htheta : (∑ p ∈ (N+1).primesBelow, Real.log p) ≤ Real.log 4 * N := by
    have he : (N+1).primesBelow = (Ioc 0 N).filter Nat.Prime := by
      ext p
      simp only [Nat.mem_primesBelow, mem_filter, mem_Ioc]
      constructor
      · rintro ⟨hpN,hp⟩; exact ⟨⟨hp.pos,by omega⟩,hp⟩
      · rintro ⟨⟨_,hpN⟩,hp⟩; exact ⟨by omega,hp⟩
    simpa only [Chebyshev.theta, Nat.floor_natCast, ← he] using
      Chebyshev.theta_le_log4_mul_x hN0.le
  have hterm (p : ℕ) (hp : p ∈ (N+1).primesBelow) :
      (N : ℝ)*(Real.log p/(p : ℝ)) ≤ ((N.factorial.factorization p : ℝ)+1)*Real.log p := by
    obtain ⟨hpN,hpp⟩ := Nat.mem_primesBelow.mp hp
    have hdiv := div_le_factorization_factorial N p hpp (by omega)
    have hlt := Nat.lt_mul_div_succ N hpp.pos
    have hnat : N ≤ p*(N.factorial.factorization p+1) :=
      hlt.le.trans (Nat.mul_le_mul_left _ (by omega))
    have hreal : (N : ℝ) ≤ (p : ℝ)*(N.factorial.factorization p+1 : ℝ) := by exact_mod_cast hnat
    have hcoef := (div_le_iff₀ (by exact_mod_cast hpp.pos : (0 : ℝ) < p)).mpr (by nlinarith : (N : ℝ) ≤ (N.factorial.factorization p+1 : ℝ)*p)
    have h := mul_le_mul_of_nonneg_right hcoef (Real.log_nonneg (by exact_mod_cast hpp.one_le : (1 : ℝ) ≤ p))
    convert h using 1 <;> ring
  have hs := sum_le_sum hterm
  rw [← mul_sum] at hs
  simp only [add_mul, one_mul, sum_add_distrib, ← log_factorial_eq_prime_sum] at hs
  have hb := factorial_log_le N
  have hfinal : (N : ℝ)*primeLogHarmonic N ≤ N*(Real.log N+Real.log 4) := by
    dsimp only [primeLogHarmonic]
    nlinarith
  nlinarith [hfinal]

lemma primeLogHarmonic_lower (N : ℕ) (hN : 0 < N) :
    Real.log N - 1 - primePowerErrorConstant ≤ primeLogHarmonic N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ht (p : ℕ) (hp : p ∈ (N+1).primesBelow) :
      (N.factorial.factorization p : ℝ)*Real.log p ≤
        N*(Real.log p/(p : ℝ) + Real.log p/((p : ℝ)*((p : ℝ)-1))) := by
    have hpp := (Nat.mem_primesBelow.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hpred : (0 : ℝ) < (p : ℝ)-1 := by have := hpp.two_le; exact_mod_cast (show 0 < (p : ℤ)-1 by omega)
    have hv : (N.factorial.factorization p : ℝ) ≤ (N : ℝ)/((p : ℝ)-1) := by
      have hn := (Nat.cast_le (α := ℝ)).mpr (Nat.factorization_factorial_le_div_pred hpp N)
      have hd := Nat.cast_div_le (m := N) (n := p-1) (α := ℝ)
      rw [Nat.cast_sub hpp.one_le, Nat.cast_one] at hd
      exact hn.trans hd
    have hm := mul_le_mul_of_nonneg_right hv (Real.log_nonneg (by exact_mod_cast hpp.one_le : (1 : ℝ) ≤ p))
    convert hm using 1 <;> field_simp <;> ring
  have hs := sum_le_sum ht
  rw [← log_factorial_eq_prime_sum, ← mul_sum, sum_add_distrib] at hs
  have he := prime_log_pred_error_sum_bound N
  have hl := factorial_log_lower N
  change Real.log N - 1 - primePowerErrorConstant ≤ ∑ p ∈ (N+1).primesBelow, Real.log p/(p : ℝ)
  nlinarith [mul_le_mul_of_nonneg_left he hN0.le]

#print axioms primeLogHarmonic_upper
#print axioms primeLogHarmonic_lower
end FiniteSieve
end Erdos371
