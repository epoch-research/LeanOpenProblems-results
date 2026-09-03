import FormalConjecturesUtil

/-! A rational upper-step bound for the radial integral in the Gaussian direction count. -/
namespace Erdos773.GaussianRadialBins
open Finset
set_option maxHeartbeats 2000000

def height (i : ℕ) : ℚ := 1600/(1600+(i:ℚ)^2)

lemma height_nonneg (i : ℕ) : 0 ≤ height i := by unfold height; positivity
lemma height_le_one (i : ℕ) : height i ≤ 1 := by
  unfold height
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg (i:ℚ)]
lemma height_sum : ∑ i ∈ range 40, height i ≤ 793/25 := by
  norm_num [sum_range_succ,height]
lemma height_sum_real : (∑ i ∈ range 40, (height i:ℝ)) ≤ 793/25 := by
  have hh := (Rat.cast_le (K := ℝ)).mpr height_sum
  simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_ofNat] using hh

lemma reciprocal_bound {u v i : ℕ} (hu : 0<u) (hlo : u*i ≤ 40*v) :
    1/((u:ℝ)^2+(v:ℝ)^2) ≤ (height i:ℝ)/(u:ℝ)^2 := by
  have huR : (0:ℝ)<u := by exact_mod_cast hu
  have hloR : (u:ℝ)*i ≤ 40*v := by exact_mod_cast hlo
  have hs := pow_le_pow_left₀ (show (0:ℝ) ≤ u*i by positivity) hloR 2
  have hi : (height i:ℝ)=1600/(1600+(i:ℝ)^2) := by norm_num [height]
  rw [hi]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<u^2+v^2) (sq_pos_of_pos huR)).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<1600+(i:ℝ)^2)).mpr
  nlinarith only [hs]

#print axioms height_sum
#print axioms reciprocal_bound
end Erdos773.GaussianRadialBins
