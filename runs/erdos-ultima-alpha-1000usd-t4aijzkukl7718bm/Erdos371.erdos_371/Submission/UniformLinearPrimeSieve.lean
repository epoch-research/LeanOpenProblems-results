import Submission.OneLinearSelberg

/-! A coarse Brun--Titchmarsh-type bound for prime values in any arithmetic
progression segment. The constant is absolute, and uniform in both slope
and intercept. -/
namespace Erdos371.FiniteSieve
open Finset
set_option autoImplicit false

noncomputable def linearPrimeSieveConstant : ℝ := 128*Real.exp 1+2^35+4

lemma linearPrimeSieveConstant_pos : 0 < linearPrimeSieveConstant := by
  unfold linearPrimeSieveConstant
  positivity

lemma totient_ratio_one_le (a : ℕ) (ha : 0 < a) : 1 ≤ (a : ℝ)/a.totient := by
  have hφ : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  exact (one_le_div hφ).mpr (by exact_mod_cast Nat.totient_le a)

lemma sqrt_le_four_nat_div_log_succ (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (N+1 : ℝ) ≤ 4*N/Real.log (N+1 : ℝ) := by
  have hx : (0 : ℝ) < N+1 := by positivity
  have hlog : 0 < Real.log (N+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N+1 by omega))
  have h := Real.log_le_rpow_div hx.le (by norm_num : (0 : ℝ) < 1/2)
  rw [← Real.sqrt_eq_rpow] at h
  have hs := Real.sq_sqrt hx.le
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply (le_div_iff₀ hlog).mpr
  nlinarith [mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (N+1 : ℝ))]

lemma sieve_power_cutoff_bounds (N : ℕ) (hN : 1 ≤ N) :
    let z := ⌊(N+1 : ℝ)^(1/64 : ℝ)⌋₊
    1 ≤ z ∧
    1/Real.log (z+1 : ℝ) ≤ 64/Real.log (N+1 : ℝ) ∧
    (z+1 : ℝ)^32 ≤ (2 : ℝ)^32*Real.sqrt (N+1 : ℝ) ∧
    (z : ℝ) ≤ Real.sqrt (N+1 : ℝ) := by
  let x : ℝ := N+1
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hpow := Real.rpow_pos_of_pos hx (1/64 : ℝ)
  have hpow1 := Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 1/64)
  let z := ⌊x^(1/64 : ℝ)⌋₊
  have hz : 1 ≤ z := (Nat.one_le_floor_iff _).mpr hpow1
  have hzf : (z : ℝ) ≤ x^(1/64 : ℝ) := Nat.floor_le hpow.le
  have hzup : (z+1 : ℝ) ≤ 2*x^(1/64 : ℝ) := by linarith
  have hzlow : x^(1/64 : ℝ) ≤ (z+1 : ℝ) := (Nat.lt_floor_add_one _).le
  have hlogx : 0 < Real.log x := Real.log_pos (by dsimp [x]; exact_mod_cast (show 1 < N+1 by omega))
  have hlogz : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  have hlogs := Real.log_le_log hpow hzlow
  rw [Real.log_rpow hx] at hlogs
  have hinv : 1/Real.log (z+1 : ℝ) ≤ 64/Real.log x := by
    apply (div_le_div_iff₀ hlogz hlogx).mpr
    linarith
  have he : (x^(1/64 : ℝ))^32 = Real.sqrt x := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
    norm_num
    exact (Real.sqrt_eq_rpow x).symm
  have hlarge : (z+1 : ℝ)^32 ≤ (2 : ℝ)^32*Real.sqrt x := by
    calc
      _ ≤ (2*x^(1/64 : ℝ))^32 := pow_le_pow_left₀ (by positivity) hzup _
      _ = _ := by rw [mul_pow,he]
  have hsmall : (z : ℝ) ≤ Real.sqrt x := by
    apply hzf.trans
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  exact ⟨hz,hinv,hlarge,hsmall⟩

/-- The estimate counts ALL prime values, including the primes below the
sieve cutoff. It is uniform in a,b and requires only a>0 and N>=1. -/
theorem linear_prime_count_uniform (a b N : ℕ) (ha : 0 < a) (hN : 1 ≤ N) :
    (((range N).filter (fun n => (a*n+b).Prime)).card : ℝ) ≤
      linearPrimeSieveConstant*((a : ℝ)/a.totient)*N/Real.log (N+1 : ℝ) := by
  let z := ⌊(N+1 : ℝ)^(1/64 : ℝ)⌋₊
  obtain ⟨hz,hinv,hpow,hsmall⟩ := sieve_power_cutoff_bounds N hN
  have hr : 1 ≤ (a : ℝ)/a.totient := totient_ratio_one_le a ha
  have hlog : 0 < Real.log (N+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N+1 by omega))
  have hmain : 2*Real.exp 1*((a : ℝ)/a.totient)*N/Real.log (z+1 : ℝ) ≤
      128*Real.exp 1*((a : ℝ)/a.totient)*N/Real.log (N+1 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hinv
      (show (0 : ℝ) ≤ 2*Real.exp 1*((a : ℝ)/a.totient)*N by positivity)
    convert h using 1 <;> ring
  have htail : 2*(z+1 : ℝ)^32+z ≤
      ((2 : ℝ)^35+4)*((a : ℝ)/a.totient)*N/Real.log (N+1 : ℝ) := by
    have hraw : 2*(z+1 : ℝ)^32+z ≤ ((2 : ℝ)^33+1)*Real.sqrt (N+1 : ℝ) := by
      change (z+1 : ℝ)^32 ≤ (2 : ℝ)^32*Real.sqrt (N+1 : ℝ) at hpow
      change (z : ℝ) ≤ Real.sqrt (N+1 : ℝ) at hsmall
      nlinarith only [hpow,hsmall]
    have h := mul_le_mul_of_nonneg_left (sqrt_le_four_nat_div_log_succ N hN)
      (show (0 : ℝ) ≤ (2 : ℝ)^33+1 by positivity)
    have hratio := mul_le_mul_of_nonneg_right hr
      (show (0 : ℝ) ≤ ((2 : ℝ)^35+4)*N/Real.log (N+1 : ℝ) by positivity)
    have hfinal : ((2 : ℝ)^33+1)*Real.sqrt (N+1 : ℝ) ≤
        ((2 : ℝ)^35+4)*((a : ℝ)/a.totient)*N/Real.log (N+1 : ℝ) := by
      calc
        _ ≤ ((2 : ℝ)^33+1)*(4*N/Real.log (N+1 : ℝ)) := h
        _ = ((2 : ℝ)^35+4)*N/Real.log (N+1 : ℝ) := by ring
        _ ≤ _ := by convert hratio using 1 <;> ring
    exact hraw.trans hfinal
  have hh := oneLinear_all_prime_count_bound a b N z ha hz
  have h := add_le_add hmain htail
  apply hh.trans
  convert h using 1
  · ring
  · unfold linearPrimeSieveConstant
    ring

#print axioms linear_prime_count_uniform
end Erdos371.FiniteSieve
