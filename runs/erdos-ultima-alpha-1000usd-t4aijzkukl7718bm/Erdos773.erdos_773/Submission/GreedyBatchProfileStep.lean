import Submission.GreedyBatchCeilingErrors

/-! The shrinking time step and coefficient slack for exponential profiles. -/
namespace Erdos773.GreedyBatchProfileStep
set_option maxHeartbeats 2500000
noncomputable section

def a (m : ℕ) : ℝ := 1-1000/(m:ℝ)^2
def A (m : ℕ) : ℝ := 3+6000/(m:ℝ)^2
def B (m : ℕ) : ℝ := 3+3000/(m:ℝ)^2
def step (m : ℕ) (t : ℝ) : ℝ := 1/((m:ℝ)^2*(1+t^2))

lemma coefficients (m : ℕ) (hm : 100≤ m) :
    3≤B m ∧ B m≤A m ∧ A m≤4 ∧ 0≤a m ∧ a m≤1 ∧
    1000/(m:ℝ)^2≤(1-1/(m:ℝ)^2)*A m-3*a m := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm2 : (10000:ℝ)≤(m:ℝ)^2 := by nlinarith only [hmR]
  have h6 : (6000:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr (by linarith only [hm2])
  have h1 : (1000:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr (by linarith only [hm2])
  have hn1 : (0:ℝ)≤1000/(m:ℝ)^2 := by positivity
  have hn3 : (0:ℝ)≤3000/(m:ℝ)^2 := by positivity
  have h36 : (3000:ℝ)/(m:ℝ)^2≤6000/(m:ℝ)^2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  refine ⟨by dsimp [B]; linarith only [hn3],by dsimp [B,A]; linarith only [h36],
    by dsimp [A]; linarith only [h6],by dsimp [a]; linarith only [h1],
    by dsimp [a]; linarith only [hn1],?_⟩
  have he : ((1-1/(m:ℝ)^2)*A m-3*a m)-1000/(m:ℝ)^2=
      (7997*(m:ℝ)^2-6000)/(m:ℝ)^4 := by
    dsimp [A,a]
    field_simp
    ring
  apply sub_nonneg.mp
  rw [he]
  exact div_nonneg (by nlinarith only [hm2]) (by positivity)

lemma step_pos (m : ℕ) (t : ℝ) (hm : 0< m) : 0<step m t := by
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  unfold step
  positivity

lemma step_bound (m : ℕ) (t : ℝ) (hm : 1≤ m) : step m t≤1/(m:ℝ)^2 := by
  have hmR : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  unfold step
  apply one_div_le_one_div_of_le (by positivity)
  have hh := mul_nonneg (sq_nonneg (m:ℝ)) (sq_nonneg t)
  nlinarith only [hh]

lemma step_le_time (m : ℕ) (t : ℝ) (hm : 1≤ m) (ht : 1≤t) : step m t≤t := by
  apply (step_bound m t hm).trans
  have hmR : (1:ℝ)≤ m := by exact_mod_cast hm
  have hh : (1:ℝ)≤(m:ℝ)^2 := one_le_pow₀ hmR
  have he : (1:ℝ)/(m:ℝ)^2≤1 := (div_le_one (by positivity)).mpr hh
  exact he.trans ht

lemma step_squared (m : ℕ) (t : ℝ) (hm : 1≤ m) : (step m t)^2≤1/(m:ℝ)^4 := by
  have hh := pow_le_pow_left₀ (step_pos m t (by omega)).le (step_bound m t hm) 2
  convert hh using 1 <;> ring

lemma step_squared_time (m : ℕ) (t : ℝ) (hm : 1≤ m) (ht : 1≤t) :
    (step m t)^2*t≤1/(m:ℝ)^4 := by
  have hmR : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have ht2 : t≤(1+t^2)^2 := by nlinarith only [ht,sq_nonneg (t^2)]
  have hr : t/(1+t^2)^2≤1 := (div_le_one (by positivity)).mpr ht2
  calc
    _ = (1/(m:ℝ)^4)*(t/(1+t^2)^2) := by unfold step; field_simp
    _ ≤ (1/(m:ℝ)^4)*1 := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := mul_one _

lemma step_time_squared (m : ℕ) (t : ℝ) (hm : 1≤ m) (ht : 1≤t) :
    1/(2*(m:ℝ)^2)≤step m t*t^2 := by
  have hmR : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have he : step m t*t^2=t^2/((m:ℝ)^2*(1+t^2)) := by unfold step; ring
  rw [he]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(m:ℝ)^2*(1+t^2))).mpr
  have he : 1/(2*(m:ℝ)^2)*((m:ℝ)^2*(1+t^2))=(1+t^2)/2 := by field_simp
  rw [he]
  nlinarith only [ht]

lemma step_gap (m : ℕ) (t : ℝ) (hm : 100≤ m) (ht : 1≤t) :
    500/(m:ℝ)^4≤((1-1/(m:ℝ)^2)*A m-3*a m)*(step m t*t^2) := by
  have hmR : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hgap := (coefficients m hm).2.2.2.2.2
  have hx := step_time_squared m t (by omega) ht
  have hh := mul_le_mul hgap hx (by positivity : (0:ℝ)≤1/(2*(m:ℝ)^2))
    ((by positivity : (0:ℝ)≤1000/(m:ℝ)^2).trans hgap)
  convert hh using 1 <;> ring

#print axioms coefficients
#print axioms step_bound
#print axioms step_squared_time
#print axioms step_time_squared
#print axioms step_gap
end
end Erdos773.GreedyBatchProfileStep
