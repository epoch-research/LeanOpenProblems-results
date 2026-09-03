import Submission.BuchstabDoublePrimeCost

/-! Uniform normalization of the complete two-prime estimate. This is the
arithmetic contraction input; the full actual recurrence is treated separately.
No quadratic Jacobsthal endpoint is asserted. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real Finset WeightedMertens ContinuousBuchstab
set_option maxHeartbeats 2200000

lemma doublePrime_main_contraction (U V L : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hUV : U ≤ V) (hVL : V ≤ L) (hUL : 3*U ≤ L) :
    exp (4/3-(2/3 : ℝ)*L/U)*(3/(4*L)) ≤
      (19/20 : ℝ)*(exp ((-2/3 : ℝ)*L/V)/V) := by
  let s := L/V
  let b := L/U-1
  have hL : 0 < L := hV.trans_le hVL
  have hs : 1 ≤ s := (one_le_div hV).mpr hVL
  have hb2 : 2 ≤ b := by
    have hh : 3 ≤ L/U := (le_div_iff₀ hU).mpr hUL
    dsimp [b]
    linarith
  have hsb : s-1 ≤ b := by
    dsimp [s,b]
    exact sub_le_sub_right (div_le_div_of_nonneg_left hL.le hU hUV) 1
  have hb : max 2 (s-1) ≤ b := max_le hb2 hsb
  have hh := exp_le_exp.mpr (show (2/3 : ℝ)*(s+1-b) ≤ (2/3 : ℝ)*(s+1-max 2 (s-1)) by linarith)
  have hm := (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 3)).trans
    (slow_exp_cutoff_comparison s hs)
  have he := mul_le_mul_of_nonneg_left exp_four_thirds_lt.le (show 0 ≤ s by linarith)
  have hc := mul_le_mul_of_nonneg_right (hm.trans he) (exp_pos ((-2/3 : ℝ)*s)).le
  have hid : exp ((2/3 : ℝ)*(s+1-b))*exp ((-2/3 : ℝ)*s)=
      exp (4/3-(2/3 : ℝ)*L/U) := by
    rw [← exp_add]
    congr 1
    dsimp [b]
    ring
  rw [mul_assoc,hid] at hc
  have heq : (-2/3 : ℝ)*s=(-2/3 : ℝ)*L/V := by dsimp [s]; ring
  rw [heq] at hc
  apply (mul_le_mul_iff_left₀ (show 0 < 4*L*V by positivity)).mp
  have he1 : exp (4/3-(2/3 : ℝ)*L/U)*(3/(4*L))*(4*L*V)=
      (3*exp (4/3-(2/3 : ℝ)*L/U))*V := by field_simp
  have he2 : (19/20 : ℝ)*(exp ((-2/3 : ℝ)*L/V)/V)*(4*L*V)=
      ((L/V)*(19/5)*exp ((-2/3 : ℝ)*L/V))*V := by field_simp; ring
  rw [he1,he2]
  exact mul_le_mul_of_nonneg_right hc hV.le

lemma doublePrime_error_coefficient (U V E : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hUV : V/4 ≤ U) (hE : 0 ≤ E) :
    8*E/U^2+80*E^2/U^3 ≤ 128*E/V^2+5120*E^2/V^3 := by
  have hi : 1/U ≤ 4/V := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < V/4) hUV
    convert hh using 1 <;> ring
  have hi2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1/U) hi 2
  have hi3 := pow_le_pow_left₀ (by positivity : 0 ≤ 1/U) hi 3
  have hm2 := mul_le_mul_of_nonneg_left hi2 (show 0 ≤ 8*E by positivity)
  have hm3 := mul_le_mul_of_nonneg_left hi3 (show 0 ≤ 80*E^2 by positivity)
  have hh := add_le_add hm2 hm3
  convert hh using 1 <;> ring

lemma doublePrime_exp_factor (U V L : ℝ) (hU : 0 < U) (hUV : U ≤ V) (hL : 0 ≤ L) :
    exp (4/3-(2/3 : ℝ)*L/U) ≤ 4*exp ((-2/3 : ℝ)*L/V) := by
  have hh := div_le_div_of_nonneg_left hL hU hUV
  have he : 4/3-(2/3 : ℝ)*L/U ≤ 4/3+(-2/3 : ℝ)*L/V := by
    have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2/3)
    have hn : (2/3 : ℝ)*L/V ≤ (2/3 : ℝ)*L/U := by
      convert hm using 1 <;> ring
    ring_nf at hn ⊢
    linarith only [hn]
  apply (exp_le_exp.mpr he).trans
  rw [exp_add]
  exact mul_le_mul_of_nonneg_right (exp_four_thirds_lt.le.trans (by norm_num)) (exp_pos _).le

lemma doublePrime_small_coefficient (V E : ℝ) (hV : 0 < V) (hE : 0 ≤ E)
    (hVE : 100000*E ≤ V) : 512*E/V+20480*E^2/V^2 ≤ (1/100 : ℝ) := by
  have hx0 : 0 ≤ E/V := div_nonneg hE hV.le
  have hx : E/V ≤ (1/100000 : ℝ) := (div_le_iff₀ hV).mpr (by linarith only [hVE])
  have hx2 := pow_le_pow_left₀ hx0 hx 2
  norm_num at hx2
  have he : 512*E/V+20480*E^2/V^2 = 512*(E/V)+20480*(E/V)^2 := by ring
  rw [he]
  nlinarith only [hx,hx2]

/-- All arithmetic remainders fit in one hundredth of the profile once the
boundary-prime logarithm exceeds a fixed multiple of the Mertens constant. -/
lemma doublePrime_remainder_contraction (U V L E : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hUV : U ≤ V) (hVU : V/4 ≤ U)
    (hL : 0 ≤ L) (hE : 0 ≤ E) (hVE : 100000*E ≤ V) :
    exp (4/3-(2/3 : ℝ)*L/U)*(8*E/U^2+80*E^2/U^3) ≤
      (1/100 : ℝ)*(exp ((-2/3 : ℝ)*L/V)/V) := by
  have he := doublePrime_exp_factor U V L hU hUV hL
  have hc := doublePrime_error_coefficient U V E hU hV hVU hE
  have hm := mul_le_mul he hc (by positivity : 0 ≤ 8*E/U^2+80*E^2/U^3)
    (by positivity : 0 ≤ 4*exp ((-2/3 : ℝ)*L/V))
  have hs := mul_le_mul_of_nonneg_right (doublePrime_small_coefficient V E hV hE hVE)
    (by positivity : 0 ≤ exp ((-2/3 : ℝ)*L/V)/V)
  apply hm.trans
  convert hs using 1 <;> ring

/-- Complete finite two-prime contraction, with all logarithmic-scale and
cutoff assumptions explicit. The contraction constant is 24/25. -/
theorem primeDoubleSlowSum_contraction (R : ℕ) (hR : 2 ≤ R) (L V : ℝ)
    (hV : 0 < V) (hVL : V ≤ L) (hUV : log (R : ℝ) ≤ V)
    (hVU : V/4 ≤ log (R : ℝ)) (hRL : 3*log (R : ℝ) ≤ L)
    (hVE : 100000*smoothProfileError ≤ V) :
    primeDoubleSlowSum R L ≤ (24/25 : ℝ)*(exp ((-2/3 : ℝ)*L/V)/V) := by
  have hU : 0 < log (R : ℝ) := log_pos (by exact_mod_cast (show 1 < R by omega))
  have hmain := doublePrime_main_contraction (log (R : ℝ)) V L hU hV hUV hVL hRL
  have herr := doublePrime_remainder_contraction (log (R : ℝ)) V L smoothProfileError
    hU hV hUV hVU (hV.le.trans hVL) smoothProfileError_pos.le hVE
  have hh := add_le_add hmain herr
  apply (primeDoubleSlowSum_upper R hR L hRL).trans
  convert hh using 1 <;> ring

#print axioms primeDoubleSlowSum_contraction
end Erdos970.RecursiveSieve.Buchstab
