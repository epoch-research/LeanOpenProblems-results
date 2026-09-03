import Submission.ShiftedPrimeFactorMean

/-!
# Positive logarithmic-power lower bounds for shifted-prime divisor moments

The exponent obtained here is proportional to log(k), not to k.  These
unconditional lower bounds are therefore weaker than the sharp fixed-order
moment input required for the full conjecture.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821.HigherDivisors
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma pow_primeFactors_card_le_tau (k n : ℕ) (hn : n ≠ 0) :
    (k+1)^n.primeFactors.card ≤ tau (k+1) n := by
  rw [tau_factorization _ _ hn,← prod_const]
  apply Finset.prod_le_prod'
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have he := hp'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  rw [tau_prime_pow k _ p hp']
  have h := Nat.choose_le_choose k (Nat.add_le_add_right he k)
  simpa only [Nat.add_comm 1 k,Nat.choose_succ_self_right] using h

lemma exp_tangent_lower (x u : ℝ) : Real.exp u*(x-u) ≤ Real.exp x := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x-u)) (Real.exp_pos u).le
  rw [← Real.exp_add] at h
  have he : u+(x-u)=x := by ring
  rw [he] at h
  nlinarith only [h,Real.exp_pos u]

noncomputable def primeLogDivisorMoment (k N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, Real.log (p : ℝ)*(tau k (p-1) : ℝ)

lemma primeLogDivisorMoment_le (k N : ℕ) :
    primeLogDivisorMoment k N ≤ Real.log N*shiftedPrimeMoment k N := by
  unfold primeLogDivisorMoment shiftedPrimeMoment
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hpN := (Nat.mem_primesBelow.mp hp).1
  exact mul_le_mul_of_nonneg_right (log_nat_mono (by omega : p ≤ N)) (Nat.cast_nonneg _)

lemma prime_log_mass_le_two (N : ℕ) :
    (∑ p ∈ (N+1).primesBelow, Real.log (p : ℝ)) ≤ 2*(N : ℝ) := by
  rw [← Sieve.theta_nat_eq_sum_primesBelow]
  apply (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)).trans
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h2 ⊢
    linarith
  exact mul_le_mul_of_nonneg_right hlog4 (Nat.cast_nonneg _)

lemma primeLogDivisorMoment_tangent (k N : ℕ) (hk : 2 ≤ k) (u : ℝ) :
    Real.exp u*(Real.log (k : ℝ)*shiftedPrimeFactorMangoldt N-
      u*(∑ p ∈ (N+1).primesBelow, Real.log (p : ℝ))) ≤ primeLogDivisorMoment k N := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpoint (p : ℕ) (hp : p ∈ (N+1).primesBelow) :
      Real.log (p : ℝ)*(Real.exp u*(Real.log (k : ℝ)*((p-1).primeFactors.card : ℝ)-u)) ≤
        Real.log (p : ℝ)*(tau k (p-1) : ℝ) := by
    have hp' := (Nat.mem_primesBelow.mp hp).2
    have hn : p-1 ≠ 0 := by have := hp'.two_le; omega
    have hpow : (k : ℝ)^((p-1).primeFactors.card) ≤ tau k (p-1) := by
      have h := pow_primeFactors_card_le_tau (k-1) (p-1) hn
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
      exact_mod_cast h
    have heq : Real.exp (Real.log (k : ℝ)*((p-1).primeFactors.card : ℝ)) =
        (k : ℝ)^((p-1).primeFactors.card) := by
      rw [← Real.rpow_natCast,Real.rpow_def_of_pos hk0]
    apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg p)
    exact (exp_tangent_lower _ u).trans (heq ▸ hpow)
  have h := sum_le_sum hpoint
  apply le_trans (le_of_eq ?_) h
  simp only [shiftedPrimeFactorMangoldt,mul_sub,mul_sum,sum_sub_distrib]
  rw [← sum_sub_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  ring

/-- A uniform exponential-in-m lower estimate for every divisor order k>=2.
The prime scale is doubly exponential in m. -/
theorem eventually_primeLogDivisorMoment_lower :
    ∀ᶠ m : ℕ in atTop, ∀ k : ℕ, 2 ≤ k →
      (logMomentX m : ℝ)*Real.exp (Real.log (k : ℝ)*(m : ℝ)/32768) ≤
        primeLogDivisorMoment k (logMomentX m) := by
  filter_upwards [eventually_shiftedPrimeFactorMangoldt_lower,eventually_ge_atTop 32768]
    with m hmean hm k hk
  let N := logMomentX m
  let ℓ := Real.log (k : ℝ)
  let u := ℓ*(m : ℝ)/32768
  have hℓ : (1/2 : ℝ) ≤ ℓ := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hkR
    have h2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact h2.trans h
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hmR : (32768 : ℝ) ≤ m := by exact_mod_cast hm
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlow := mul_le_mul_of_nonneg_left hmean hℓ0
  have hmass := mul_le_mul_of_nonneg_left (prime_log_mass_le_two N) hu
  have hℓm : 16384 ≤ ℓ*(m : ℝ) := by nlinarith only [hℓ,hmR,mul_nonneg (sub_nonneg.mpr hℓ) (sub_nonneg.mpr hmR)]
  have hNm := mul_le_mul_of_nonneg_left hℓm hN
  have hinside : (N : ℝ) ≤ ℓ*shiftedPrimeFactorMangoldt N-
      u*(∑ p ∈ (N+1).primesBelow, Real.log (p : ℝ)) := by
    dsimp only [u] at hmass ⊢
    change ℓ*((N : ℝ)*(m : ℝ)/8192) ≤ ℓ*shiftedPrimeFactorMangoldt N at hlow
    nlinarith only [hlow,hmass,hNm]
  have h := (mul_le_mul_of_nonneg_left hinside (Real.exp_pos u).le).trans
    (primeLogDivisorMoment_tangent k N hk u)
  simpa only [u,ℓ,mul_comm] using h

lemma log_logMomentX_pos (m : ℕ) : 0 < Real.log (logMomentX m : ℝ) := by
  apply Real.log_pos
  have hE := logMomentScale_ge m
  have hN : 1 < logMomentX m := by
    unfold logMomentX progressionScaleN
    exact Nat.one_lt_pow (by nlinarith : 64*(logMomentScale m*logMomentScale m) ≠ 0) (by decide)
  exact_mod_cast hN

lemma log_log_logMomentX_le (m : ℕ) (hm : 8 ≤ m) :
    Real.log (Real.log (logMomentX m : ℝ)) ≤ 4*(m : ℝ) := by
  have hlog := log_two_pow_le (64*(logMomentScale m*logMomentScale m))
  change Real.log (logMomentX m : ℝ) ≤ ((64*(logMomentScale m*logMomentScale m) : ℕ) : ℝ) at hlog
  have heq : 64*(logMomentScale m*logMomentScale m) = 2^(2*m+16) := by
    unfold logMomentScale
    rw [show (64 : ℕ) = 2^6 by decide,← pow_add,← pow_add]
    congr 1
    omega
  rw [heq] at hlog
  have h := (Real.log_le_log (log_logMomentX_pos m) hlog).trans (log_two_pow_le (2*m+16))
  have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast at h
  linarith

/-- A positive logarithmic-power lower bound, uniform over k>=2. Its power
is log(k)/131072, not the conjecturally expected k-1. -/
theorem eventually_shiftedPrimeMoment_log_power_lower :
    ∀ᶠ m : ℕ in atTop, ∀ k : ℕ, 2 ≤ k →
      (logMomentX m : ℝ)*(Real.log (logMomentX m : ℝ))^(Real.log (k : ℝ)/131072-1) ≤
        shiftedPrimeMoment k (logMomentX m) := by
  filter_upwards [eventually_primeLogDivisorMoment_lower,eventually_ge_atTop 8] with m hm hm8 k hk
  let N := logMomentX m
  let η := Real.log (k : ℝ)/131072
  have hlog : 0 < Real.log (N : ℝ) := log_logMomentX_pos m
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hη : 0 ≤ η := div_nonneg (Real.log_nonneg hk1) (by norm_num)
  have hpow : (Real.log (N : ℝ))^η ≤ Real.exp (Real.log (k : ℝ)*(m : ℝ)/32768) := by
    rw [Real.rpow_def_of_pos hlog]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (log_log_logMomentX_le m hm8) hη
    convert h using 1
    dsimp [η,N]
    ring
  have hbound := (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N)).trans
    ((hm k hk).trans (primeLogDivisorMoment_le k N))
  have heq : (Real.log (N : ℝ))^(η-1) = (Real.log (N : ℝ))^η/Real.log (N : ℝ) := by
    rw [Real.rpow_sub hlog,Real.rpow_one]
  change (N : ℝ)*(Real.log (N : ℝ))^(η-1) ≤ _
  rw [heq,← mul_div_assoc]
  apply (div_le_iff₀ hlog).mpr
  simpa only [mul_comm] using hbound

lemma logMomentX_eq_tower (m : ℕ) : logMomentX m = 2^(2^(2*m+16)) := by
  unfold logMomentX progressionScaleN logMomentScale
  apply congrArg (fun e : ℕ => (2 : ℕ)^e)
  rw [show (64 : ℕ) = 2^6 by decide,← pow_add,← pow_add]
  congr 1
  omega

/-- Even order two now has an explicit positive power of log(X) beyond
X/log(X), rather than an unspecified unbounded multiplier. -/
theorem eventually_shiftedPrimeMoment_two_log_power_lower :
    ∀ᶠ m : ℕ in atTop,
      (logMomentX m : ℝ)*(Real.log (logMomentX m : ℝ))^((1/262144 : ℝ)-1) ≤
        shiftedPrimeMoment 2 (logMomentX m) := by
  filter_upwards [eventually_shiftedPrimeMoment_log_power_lower] with m hm
  have hlog1 : 1 ≤ Real.log (logMomentX m : ℝ) := by
    have hE := logMomentScale_ge m
    have hT : (1 : ℝ) ≤ (logMomentScale m*logMomentScale m : ℕ) := by
      exact_mod_cast (show 1 ≤ logMomentScale m*logMomentScale m by nlinarith)
    exact hT.trans (log_progression_scale_ge _)
  apply le_trans _ (hm 2 (by decide))
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le hlog1
  have h2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  norm_num only [Nat.cast_ofNat]
  linarith only [h2]

end Erdos821.HigherDivisors
