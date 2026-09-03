import Submission.IndependentCompositeGain

/-!
# A limitation of the independent-parameter sufficient conditions

This is a numerical obstruction to choosing parameters in the preceding method.
It is not an upper bound on inverse-totient multiplicities or on the actual
smooth-prime count.
-/

namespace Erdos821

lemma independent_parameters_cutoff_bound (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (17/32 : ℝ)*((b : ℝ)-1)^2) :
    489*t < 1000*b := by
  by_contra hn
  have hbt : (b : ℝ) ≤ (489/1000 : ℝ)*t := by
    have hn' : 1000*b ≤ 489*t := by omega
    have hnR : (1000 : ℝ)*b ≤ 489*t := by exact_mod_cast hn'
    linarith only [hnR]
  have heqR : (r : ℝ)+b+h=t := by exact_mod_cast heq
  have hrtR : 2*(r : ℝ)+1 ≤ t := by exact_mod_cast hrt
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have ht : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hh : (11/1000 : ℝ)*t ≤ (h : ℝ) := by linarith only [heqR, hrtR, hbt]
  have hprod := mul_le_mul_of_nonneg_left hh ht.le
  have hsquare : ((b : ℝ)-1)^2 ≤ ((489/1000 : ℝ)*t)^2 := by
    apply pow_le_pow_left₀ (by linarith only [hbR]) (by linarith only [hbt])
  have hu := hc.trans (mul_le_mul_of_nonneg_left hsquare (by norm_num : (0 : ℝ) ≤ 17/32))
  nlinarith only [hprod, hu, sq_pos_of_pos ht]

/-- Every exponent threshold provided by these parameter conditions is below 0.511. -/
lemma independent_parameters_exponent_bound (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b)
    (hc : (8320/675 : ℝ)*(t : ℝ)*h ≤ (17/32 : ℝ)*((b : ℝ)-1)^2) :
    1-(b : ℝ)/t < 511/1000 := by
  have ht : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hb' := independent_parameters_cutoff_bound r t b h heq hrt hb hc
  have hbR : (489 : ℝ)*t < 1000*b := by exact_mod_cast hb'
  have hdiv : (489/1000 : ℝ) < (b : ℝ)/t := by
    apply (lt_div_iff₀ ht).mpr
    linarith only [hbR]
  linarith only [hdiv]

end Erdos821
