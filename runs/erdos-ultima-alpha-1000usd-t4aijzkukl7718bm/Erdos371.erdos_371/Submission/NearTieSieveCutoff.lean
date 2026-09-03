import Submission.LargePrimeNearTies

/-! An explicit sieve cutoff whose main-term saving exceeds one logarithm
while the accumulated CRT error remains subpower. -/

namespace Erdos371
namespace FiniteSieve
open Filter

lemma natLog_two_le_two_log (z : ℕ) :
    (Nat.log 2 z : ℝ) ≤ 2*Real.log z := by
  have h := Real.natLog_le_logb z 2
  simp only [Nat.cast_ofNat, Real.logb] at h
  have hl : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hz := Real.log_natCast_nonneg z
  refine h.trans ((div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr ?_)
  nlinarith

lemma brunDegree_sqrt_log_bound (z : ℕ) :
    (brunDegree z : ℝ) ≤ 600*(Real.sqrt (Real.log z)+1) := by
  have h1 := natLog_two_le_two_log z
  have h2 := natLog_two_le_two_log (Nat.log 2 z)
  have h3 := Real.log_le_rpow_div (Nat.cast_nonneg (α := ℝ) (Nat.log 2 z))
    (by norm_num : (0 : ℝ) < 1/2)
  rw [← Real.sqrt_eq_rpow] at h3
  have hs : Real.sqrt (Nat.log 2 z : ℝ) ≤ 2*Real.sqrt (Real.log z) := by
    apply (Real.sqrt_le_iff).mpr ⟨by positivity, ?_⟩
    have hlog := Real.log_natCast_nonneg z
    have he := Real.sq_sqrt hlog
    nlinarith
  have hsqrt := Real.sqrt_nonneg (Real.log z)
  simp only [brunDegree, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  nlinarith

noncomputable def nearTieSieveCutoff (N : ℕ) : ℕ :=
  ⌊Real.exp ((Real.log N)^(3/5 : ℝ))⌋₊

lemma nearTieSieveCutoff_one_le (N : ℕ) : 1 ≤ nearTieSieveCutoff N := by
  apply (Nat.one_le_floor_iff _).mpr
  exact Real.one_le_exp_iff.mpr (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)

lemma nearTieSieveCutoff_log_bounds (N : ℕ) :
    Real.log (nearTieSieveCutoff N) ≤ (Real.log N)^(3/5 : ℝ) ∧
    (Real.log N)^(3/5 : ℝ) ≤ Real.log (nearTieSieveCutoff N+1 : ℝ) ∧
    Real.log (nearTieSieveCutoff N+1 : ℝ) ≤ (Real.log N)^(3/5 : ℝ) + Real.log 2 := by
  let L := (Real.log N)^(3/5 : ℝ)
  have hL : 0 ≤ L := Real.rpow_nonneg (Real.log_natCast_nonneg N) _
  have he : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have hz0 : (0 : ℝ) < nearTieSieveCutoff N := by
    exact_mod_cast (show 0 < nearTieSieveCutoff N from nearTieSieveCutoff_one_le N)
  have hf : (nearTieSieveCutoff N : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_nonneg _)
  have hf' : Real.exp L < (nearTieSieveCutoff N : ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Real.log_exp] using Real.log_le_log hz0 hf
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos L) hf'.le
  · have ht : (nearTieSieveCutoff N : ℝ)+1 ≤ 2*Real.exp L := by linarith
    have h := Real.log_le_log (by positivity : 0 < (nearTieSieveCutoff N : ℝ)+1) ht
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero L), Real.log_exp] at h
    simpa only [add_comm] using h

noncomputable def brunRoundingError (z : ℕ) : ℝ :=
  (2*brunDegree z+1 : ℕ) * (z : ℝ)^(4*brunDegree z)

lemma brunRoundingError_pos (z : ℕ) (hz : 1 ≤ z) : 0 < brunRoundingError z := by
  unfold brunRoundingError
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  positivity

/-- A deliberately rough logarithmic bound is sufficient for the rounding error. -/
lemma brunRoundingError_log_le (N : ℕ) (hN : 1 ≤ Real.log N) :
    Real.log (brunRoundingError (nearTieSieveCutoff N)) ≤
      7200*(Real.log N)^(9/10 : ℝ) := by
  let z := nearTieSieveCutoff N
  let L := (Real.log N)^(3/5 : ℝ)
  let k := brunDegree z
  have hL : 1 ≤ L := Real.one_le_rpow hN (by norm_num)
  have hlog := (nearTieSieveCutoff_log_bounds N).1
  change Real.log z ≤ L at hlog
  have hk : (k : ℝ) ≤ 600*(Real.sqrt L+1) :=
    (brunDegree_sqrt_log_bound z).trans (by gcongr)
  have hL0 : 0 ≤ L := by linarith
  have hs : 1 ≤ Real.sqrt L := (Real.le_sqrt (by norm_num) hL0).mpr (by simpa)
  have hz : (z : ℝ) ≠ 0 := by exact_mod_cast (show z ≠ 0 from (by have := nearTieSieveCutoff_one_le N; omega))
  have hpre : Real.log (2*k+1 : ℕ) ≤ 2*k := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2*k+1 : ℕ) by positivity)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_sub_cancel_right] using h
  have he : Real.log (brunRoundingError z) = Real.log (2*k+1 : ℕ) + (4*k : ℕ)*Real.log z := by
    rw [brunRoundingError, Real.log_mul (by positivity) (pow_ne_zero _ hz), Real.log_pow]
  have hbound : Real.log (brunRoundingError z) ≤ 7200*(L*Real.sqrt L) := by
    rw [he]
    have hkl := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ (4*k : ℕ) by positivity)
    have hk' : (k : ℝ) ≤ 1200*Real.sqrt L := by nlinarith
    have ht := mul_le_mul_of_nonneg_right hk' (show 0 ≤ 2+4*L by positivity)
    have hs0 := Real.sqrt_nonneg L
    have hLL : 2+4*L ≤ 6*L := by linarith
    have ht' := mul_le_mul_of_nonneg_left hLL (show 0 ≤ 1200*Real.sqrt L by positivity)
    push_cast at hpre hkl ⊢
    nlinarith
  have hpow : L*Real.sqrt L = (Real.log N)^(9/10 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    dsimp [L]
    rw [← Real.rpow_mul (Real.log_natCast_nonneg N), ← Real.rpow_add (by linarith : 0 < Real.log N)]
    norm_num
  simpa only [hpow] using hbound

lemma logPower_div_log_tendsto_zero (a : ℝ) (ha : a < 1) :
    Tendsto (fun N : ℕ => (Real.log N)^a / Real.log N) atTop (nhds 0) := by
  have ht := (tendsto_rpow_neg_atTop (show 0 < 1-a by linarith)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply ht.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hN
  dsimp only [Function.comp_def] at hN ⊢
  have he : -(1-a) = a-1 := by ring
  rw [he, Real.rpow_sub hN, Real.rpow_one]

lemma nearTieSieveCutoff_main_ratio_bound (N : ℕ) (hN : 1 ≤ Real.log N) :
    (1+Real.log N)/(Real.log (nearTieSieveCutoff N+1 : ℝ))^2 ≤
      2*(Real.log N)^(-(1/5 : ℝ)) := by
  let L := (Real.log N)^(3/5 : ℝ)
  have hL : 1 ≤ L := Real.one_le_rpow hN (by norm_num)
  have hlog := (nearTieSieveCutoff_log_bounds N).2.1
  have hN0 : 0 < Real.log N := by linarith
  have hL0 : 0 < L := by linarith
  have hd : L^2 ≤ (Real.log (nearTieSieveCutoff N+1 : ℝ))^2 := pow_le_pow_left₀ hL0.le hlog 2
  have hpow : L^2 = (Real.log N)^(6/5 : ℝ) := by
    rw [← Real.rpow_natCast]
    dsimp [L]
    rw [← Real.rpow_mul hN0.le]
    norm_num
  have he : (Real.log N)/(Real.log N)^(6/5 : ℝ) = (Real.log N)^(-(1/5 : ℝ)) := by
    rw [show -(1/5 : ℝ) = 1-6/5 by norm_num, Real.rpow_sub hN0, Real.rpow_one]
  calc
    _ ≤ 2*Real.log N/(Real.log (nearTieSieveCutoff N+1 : ℝ))^2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ ≤ 2*Real.log N/L^2 := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hL0) hd
    _ = _ := by rw [hpow, mul_div_assoc, he]

lemma nearTieSieveCutoff_main_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => (1+Real.log N)/(Real.log (nearTieSieveCutoff N+1 : ℝ))^2)
      atTop (nhds 0) := by
  have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/5)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul (2 : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · exact Filter.Eventually.of_forall fun N => div_nonneg (by have := Real.log_natCast_nonneg N; positivity) (sq_nonneg _)
  · filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with N hN
    exact nearTieSieveCutoff_main_ratio_bound N hN

lemma nearTieSieveCutoff_subpower :
    Tendsto (fun N : ℕ => Real.log (nearTieSieveCutoff N+1 : ℝ)/Real.log N) atTop (nhds 0) := by
  have h1 := logPower_div_log_tendsto_zero (3/5) (by norm_num)
  have h2 := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul (Real.log 2)
  have ht := h1.add h2
  simp only [mul_zero, add_zero, Function.comp_def, ← div_eq_mul_inv] at ht
  apply squeeze_zero (fun N => div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (nearTieSieveCutoff N); linarith)) (Real.log_natCast_nonneg N)) _ ht
  intro N
  simpa only [add_div] using div_le_div_of_nonneg_right (nearTieSieveCutoff_log_bounds N).2.2
    (Real.log_natCast_nonneg N)

/-- For every positive exponent, the complete accumulated rounding error
is eventually smaller than that power of the averaging endpoint. -/
theorem brunRoundingError_eventually_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, brunRoundingError (nearTieSieveCutoff N) ≤ (N : ℝ)^ε := by
  have ht := (logPower_div_log_tendsto_zero (9/10) (by norm_num)).const_mul (7200 : ℝ)
  simp only [mul_zero] at ht
  filter_upwards [(tendsto_order.mp ht).2 ε hε,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℕ)] with N hsmall hlog hN
  dsimp only [Function.comp_def] at hlog
  have hlog0 : 0 < Real.log N := by linarith
  have hmain : 7200*(Real.log N)^(9/10 : ℝ) ≤ ε*Real.log N := by
    apply (div_le_iff₀ hlog0).mp
    simpa only [mul_div_assoc] using hsmall.le
  exact Real.le_rpow_of_log_le (by exact_mod_cast hN)
    ((brunRoundingError_log_le N hlog).trans hmain)

#print axioms nearTieSieveCutoff_main_ratio_tendsto_zero
#print axioms nearTieSieveCutoff_subpower
#print axioms brunRoundingError_eventually_le_rpow
#print axioms brunRoundingError_log_le
end FiniteSieve
end Erdos371
