import Submission.GreedyUniformCosts

/-!
Integer stopping thresholds and run lengths. Rounding is handled explicitly,
including readiness, the ratio needed in the common-neighbor tail, and the
loss of at most one vertex in the final independent set.
-/
namespace Erdos773.GreedyRoundedHorizon
open GreedyProfileRecords GreedyProfileGuard GreedyTrajectoryCalculus
set_option maxHeartbeats 2500000
noncomputable section

def stop (V τ : ℝ) : ℕ := ⌊V*q τ/2⌋₊
def steps (V d τ : ℝ) : ℕ := ⌊V*τ/d⌋₊

lemma stop_pos {V τ : ℝ} (h : 4 ≤ V*q τ) : 0 < stop V τ := by
  apply Nat.floor_pos.mpr
  linarith only [h]

lemma stop_lower {V τ : ℝ} (h : 4 ≤ V*q τ) : V*q τ/4 ≤ (stop V τ:ℝ) := by
  have hh := Nat.lt_floor_add_one (V*q τ/2)
  change V*q τ/4 ≤ (⌊V*q τ/2⌋₊:ℝ)
  linarith only [h,hh]

lemma stop_upper {V τ : ℝ} (hV : 0 ≤ V) : (stop V τ:ℝ) ≤ V*q τ/2 := by
  have hq := (q_pos τ).le
  exact Nat.floor_le (by positivity)

lemma steps_upper {V d τ : ℝ} (hV : 0 ≤ V) (hd : 0 ≤ d) (hτ : 0 ≤ τ) :
    (steps V d τ:ℝ) ≤ V*τ/d := Nat.floor_le (by positivity)

lemma steps_lower (V d τ : ℝ) : V*τ/d-1 ≤ (steps V d τ:ℝ) := by
  have hh := Nat.lt_floor_add_one (V*τ/d)
  change V*τ/d-1 ≤ (⌊V*τ/d⌋₊:ℝ)
  linarith only [hh]

lemma horizon {p : Parameters} {C : ℕ} {τ : ℝ}
    (hb : GreedyUniformHorizon.Bounds p.V p.d p.rho p.K τ C) (hq : 4 ≤ p.V*q τ) :
    Horizon p (stop p.V τ) (steps p.V p.d τ) C τ := by
  have hd : 0 < p.d := by linarith only [hb.d_one_le]
  refine ⟨hb,?_,stop_pos hq,?_⟩
  · have hm := mul_le_mul_of_nonneg_right (steps_upper hb.V_pos.le hd.le hb.horizon_nonneg)
      (div_nonneg hd.le hb.V_pos.le)
    change (steps p.V p.d τ:ℝ)*(p.d/p.V) ≤ τ
    calc
      _ ≤ (p.V*τ/p.d)*(p.d/p.V) := hm
      _ = τ := by field_simp [hb.V_pos.ne']
  · have hh := stop_upper (τ := τ) hb.V_pos.le
    have hn := mul_nonneg hb.V_pos.le (q_pos τ).le
    linarith only [hh,hn]

lemma ratio_bound {V d τ : ℝ} (hV : 0 < V) (hd : 0 < d) (hτ : 0 ≤ τ)
    (hq : 4 ≤ V*q τ) : (steps V d τ:ℝ)/(stop V τ:ℝ) ≤ 4*τ/(d*q τ) := by
  have hqpos := q_pos τ
  have hLpos : (0:ℝ) < (stop V τ:ℝ) := by exact_mod_cast stop_pos hq
  calc
    _ ≤ (V*τ/d)/(stop V τ:ℝ) := div_le_div_of_nonneg_right (steps_upper hV.le hd.le hτ) hLpos.le
    _ ≤ (V*τ/d)/(V*q τ/4) := div_le_div_of_nonneg_left (by positivity) (by positivity) (stop_lower hq)
    _ = _ := by field_simp

lemma steps_le_stop {V d τ : ℝ} (hV : 0 < V) (hd : 0 < d) (hτ : 0 ≤ τ)
    (hq : 4 ≤ V*q τ) (hshort : 4*τ ≤ d*q τ) : steps V d τ ≤ stop V τ := by
  have hLpos : (0:ℝ) < (stop V τ:ℝ) := by exact_mod_cast stop_pos hq
  have hh := (ratio_bound hV hd hτ hq).trans ((div_le_one (mul_pos hd (q_pos τ))).mpr hshort)
  exact_mod_cast (div_le_one hLpos).mp hh

lemma steps_half {V d τ : ℝ} (h : 2 ≤ V*τ/d) : V*τ/(2*d) ≤ (steps V d τ:ℝ) := by
  have hh := steps_lower V d τ
  have he : V*τ/(2*d) = (V*τ/d)/2 := by ring
  rw [he]
  linarith only [h,hh]

#print axioms horizon
#print axioms ratio_bound
#print axioms steps_le_stop
#print axioms steps_half
end
end Erdos773.GreedyRoundedHorizon
