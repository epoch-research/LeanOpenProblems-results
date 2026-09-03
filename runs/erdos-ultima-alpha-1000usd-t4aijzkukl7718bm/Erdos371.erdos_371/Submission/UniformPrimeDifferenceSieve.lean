import Submission.PrimeDifferenceSieve

/-! A prime-pair bound uniform in the nonzero difference, and a bounded
second moment for the singular factor as that difference varies. -/
namespace Erdos371.FiniteSieve
open Finset
set_option autoImplicit false

noncomputable def primeDifferenceSieveConstant : ℝ := 32768*Real.exp 2+2^70+64

lemma slopeSieveFactor_one_le (k : ℕ) : 1 ≤ slopeSieveFactor k := by
  unfold slopeSieveFactor
  apply Real.one_le_exp_iff.mpr
  exact mul_nonneg (by norm_num) (sum_nonneg fun _ _ => by positivity)

lemma sqrt_le_thirtytwo_nat_div_log_sq (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (N+1 : ℝ) ≤ 32*N/(Real.log (N+1 : ℝ))^2 := by
  let x : ℝ := N+1
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hlog : 0 < Real.log x := Real.log_pos (by dsimp [x]; exact_mod_cast (show 1<N+1 by omega))
  have hh := Real.log_le_rpow_div hx.le (by norm_num : (0 : ℝ)<1/4)
  have hsq := pow_le_pow_left₀ hlog.le hh 2
  have he : (x^(1/4 : ℝ))^2 = Real.sqrt x := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
    norm_num
    exact (Real.sqrt_eq_rpow x).symm
  have hlogs : (Real.log x)^2 ≤ 16*Real.sqrt x := by
    calc
      _ ≤ (x^(1/4 : ℝ)/(1/4 : ℝ))^2 := hsq
      _ = _ := by rw [div_pow,he]; ring
  have hmul := mul_le_mul_of_nonneg_left hlogs (Real.sqrt_nonneg x)
  have hs := Real.sq_sqrt hx.le
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
  change Real.sqrt x*(Real.log x)^2 ≤ 32*N
  dsimp [x] at hs
  nlinarith

lemma double_sieve_power_cutoff_bounds (N : ℕ) (hN : 1 ≤ N) :
    let z := ⌊(N+1 : ℝ)^(1/128 : ℝ)⌋₊
    1 ≤ z ∧
    1/(Real.log (z+1 : ℝ))^2 ≤ 128^2/(Real.log (N+1 : ℝ))^2 ∧
    (z+1 : ℝ)^64 ≤ (2 : ℝ)^64*Real.sqrt (N+1 : ℝ) ∧
    (z+1 : ℝ) ≤ 2*Real.sqrt (N+1 : ℝ) := by
  let x : ℝ := N+1
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hpow := Real.rpow_pos_of_pos hx (1/128 : ℝ)
  have hpow1 := Real.one_le_rpow hx1 (by norm_num : (0 : ℝ)≤1/128)
  let z := ⌊x^(1/128 : ℝ)⌋₊
  have hz : 1 ≤ z := (Nat.one_le_floor_iff _).mpr hpow1
  have hzf : (z : ℝ) ≤ x^(1/128 : ℝ) := Nat.floor_le hpow.le
  have hzup : (z+1 : ℝ) ≤ 2*x^(1/128 : ℝ) := by linarith
  have hzlow : x^(1/128 : ℝ) ≤ (z+1 : ℝ) := (Nat.lt_floor_add_one _).le
  have hlogx : 0 < Real.log x := Real.log_pos (by dsimp [x]; exact_mod_cast (show 1<N+1 by omega))
  have hlogz : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1<z+1 by omega))
  have hlogs := Real.log_le_log hpow hzlow
  rw [Real.log_rpow hx] at hlogs
  have hinv : 1/Real.log (z+1 : ℝ) ≤ 128/Real.log x := by
    apply (div_le_div_iff₀ hlogz hlogx).mpr
    linarith
  have hinv2 : 1/(Real.log (z+1 : ℝ))^2 ≤ 128^2/(Real.log x)^2 := by
    simpa only [div_pow,one_pow] using pow_le_pow_left₀ (by positivity) hinv 2
  have he : (x^(1/128 : ℝ))^64 = Real.sqrt x := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
    norm_num
    exact (Real.sqrt_eq_rpow x).symm
  have hlarge : (z+1 : ℝ)^64 ≤ (2 : ℝ)^64*Real.sqrt x := by
    calc
      _ ≤ (2*x^(1/128 : ℝ))^64 := pow_le_pow_left₀ (by positivity) hzup _
      _ = _ := by rw [mul_pow,he]
  have hsmall : (z+1 : ℝ) ≤ 2*Real.sqrt x := by
    apply hzup.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  exact ⟨hz,hinv2,hlarge,hsmall⟩

/-- All prime pairs n,n+k are counted, including primes below the sieve
cutoff. The same absolute constant works for every k>0. -/
theorem primeDifference_count_uniform (k N : ℕ) (hk : 0 < k) (hN : 1 ≤ N) :
    (((range N).filter (fun n => n.Prime ∧ (n+k).Prime)).card : ℝ) ≤
      primeDifferenceSieveConstant*slopeSieveFactor (2*k)*N/(Real.log (N+1 : ℝ))^2 := by
  let z := ⌊(N+1 : ℝ)^(1/128 : ℝ)⌋₊
  obtain ⟨hz,hinv,hpow,hsmall⟩ := double_sieve_power_cutoff_bounds N hN
  have hr := slopeSieveFactor_one_le (2*k)
  have hmain : 2*Real.exp 2*slopeSieveFactor (2*k)*N/(Real.log (z+1 : ℝ))^2 ≤
      32768*Real.exp 2*slopeSieveFactor (2*k)*N/(Real.log (N+1 : ℝ))^2 := by
    have h := mul_le_mul_of_nonneg_left hinv
      (show (0 : ℝ) ≤ 2*Real.exp 2*slopeSieveFactor (2*k)*N by unfold slopeSieveFactor; positivity)
    convert h using 1 <;> ring
  have htail : 2*(z+1 : ℝ)^64+(z+1) ≤
      ((2 : ℝ)^70+64)*slopeSieveFactor (2*k)*N/(Real.log (N+1 : ℝ))^2 := by
    have hraw : 2*(z+1 : ℝ)^64+(z+1) ≤ ((2 : ℝ)^65+2)*Real.sqrt (N+1 : ℝ) := by
      change (z+1 : ℝ)^64 ≤ (2 : ℝ)^64*Real.sqrt (N+1 : ℝ) at hpow
      change (z+1 : ℝ) ≤ 2*Real.sqrt (N+1 : ℝ) at hsmall
      nlinarith only [hpow,hsmall]
    have h := mul_le_mul_of_nonneg_left (sqrt_le_thirtytwo_nat_div_log_sq N hN)
      (show (0 : ℝ) ≤ (2 : ℝ)^65+2 by positivity)
    have hratio := mul_le_mul_of_nonneg_right hr
      (show (0 : ℝ) ≤ ((2 : ℝ)^70+64)*N/(Real.log (N+1 : ℝ))^2 by positivity)
    calc
      _ ≤ ((2 : ℝ)^65+2)*Real.sqrt (N+1 : ℝ) := hraw
      _ ≤ ((2 : ℝ)^65+2)*(32*N/(Real.log (N+1 : ℝ))^2) := h
      _ = ((2 : ℝ)^70+64)*N/(Real.log (N+1 : ℝ))^2 := by ring
      _ ≤ _ := by convert hratio using 1 <;> ring
  have hh := primeDifference_all_count_bound k N z hk hz
  have he := add_le_add hmain htail
  apply hh.trans
  convert he using 1
  · ring
  · unfold primeDifferenceSieveConstant
    ring

/-- The difference-dependent factor has a bounded second moment. -/
theorem primeDifference_factor_second_moment (N : ℕ) :
    (∑ k ∈ range N, (slopeSieveFactor (2*(k+1)))^2) ≤ N*Real.exp 18 := by
  have hm (k : ℕ) : (slopeSieveFactor (2*(k+1)))^2 ≤ (Real.exp 1)^2*(slopeSieveFactor (k+1))^2 := by
    have hh := slopeSieveFactor_mul_le 2 (k+1) (by norm_num) (by omega)
    have htwo : slopeSieveFactor 2 = Real.exp 1 := by norm_num [slopeSieveFactor,slopePrimeMass]
    rw [htwo] at hh
    simpa only [mul_pow] using pow_le_pow_left₀ (Real.exp_nonneg _) hh 2
  calc
    _ ≤ ∑ k ∈ range N, (Real.exp 1)^2*(slopeSieveFactor (k+1))^2 := sum_le_sum fun k _ => hm k
    _ = (Real.exp 1)^2*(∑ k ∈ range N, (slopeSieveFactor (k+1))^2) := by rw [mul_sum]
    _ ≤ (Real.exp 1)^2*(N*Real.exp 16) :=
      mul_le_mul_of_nonneg_left (slopeSieveFactor_second_moment N) (sq_nonneg _)
    _ = _ := by rw [sq,← Real.exp_add]; rw [mul_left_comm,← Real.exp_add]; norm_num

#print axioms primeDifference_count_uniform
#print axioms primeDifference_factor_second_moment
end Erdos371.FiniteSieve
