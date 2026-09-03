import Submission.GreedyTrajectoryCalculus

/-!
Physical scaling of the four-uniform trajectory. A time step is d/V when
the original degree is d^3. All remainder estimates are finite inequalities.
-/
namespace Erdos773.GreedyScaledTrajectory
open GreedyTrajectoryCalculus
set_option maxHeartbeats 2500000
noncomputable section

def F2 (d t : ℝ) : ℝ := d*a2 t
def F3 (d t : ℝ) : ℝ := d^2*a3 t
def F4 (d t : ℝ) : ℝ := d^3*a4 t
def Q (V t : ℝ) : ℝ := V*q t

def M2 (d t : ℝ) : ℝ := 2*F3 d t-(F2 d t)^2
def M3 (d t : ℝ) : ℝ := 3*F4 d t-2*F2 d t*F3 d t
def M4 (d t : ℝ) : ℝ := -3*F2 d t*F4 d t

lemma model_scaling (d t : ℝ) :
    M2 d t = d*d*q t*da2 t ∧ M3 d t = d*d^2*q t*da3 t ∧
      M4 d t = d*d^3*q t*da4 t := by
  have hm := mean_field t
  dsimp [M2,M3,M4,F2,F3,F4]
  constructor
  · linear_combination -(d^2)*hm.1
  constructor
  · linear_combination -(d^3)*hm.2.1
  · linear_combination -(d^4)*hm.2.2

lemma scaled_residual (f df : ℝ → ℝ) (V d scale t τ : ℝ)
    (hV : 0 < V) (hscale : 0 ≤ scale)
    (hf : |f (t+d/V)-f t-df t*(d/V)| ≤ 200*(1+τ)^6*(d/V)^2) :
    |d*scale*q t*df t-Q V t*(scale*f (t+d/V)-scale*f t)| ≤
      200*(1+τ)^6*(scale*d^2/V)*q t := by
  have he : d*scale*q t*df t-Q V t*(scale*f (t+d/V)-scale*f t) =
      (V*q t*scale)*(-(f (t+d/V)-f t-df t*(d/V))) := by
    dsimp [Q]
    field_simp
    ring
  rw [he,abs_mul,abs_of_nonneg (mul_nonneg (mul_nonneg hV.le (q_pos t).le) hscale),abs_neg]
  calc
    _ ≤ (V*q t*scale)*(200*(1+τ)^6*(d/V)^2) :=
      mul_le_mul_of_nonneg_left hf (mul_nonneg (mul_nonneg hV.le (q_pos t).le) hscale)
    _ = _ := by field_simp

/-- Mean-field residuals after a single physical step, for d_2,d_3,d_4. -/
theorem residuals {V d t τ : ℝ} (hV : 0 < V) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hτ : t+d/V ≤ τ) :
    |M2 d t-Q V t*(F2 d (t+d/V)-F2 d t)| ≤ 200*(1+τ)^6*(d^3/V)*q t ∧
    |M3 d t-Q V t*(F3 d (t+d/V)-F3 d t)| ≤ 200*(1+τ)^6*(d^4/V)*q t ∧
    |M4 d t-Q V t*(F4 d (t+d/V)-F4 d t)| ≤ 200*(1+τ)^6*(d^5/V)*q t := by
  have hr := profile_remainders ht (div_nonneg hd hV.le) hτ
  have hm := model_scaling d t
  refine ⟨?_,?_,?_⟩
  · rw [hm.1]
    convert scaled_residual a2 da2 V d d t τ hV hd hr.1 using 1
    dsimp [F2]
    ring
  · rw [hm.2.1]
    convert scaled_residual a3 da3 V d (d^2) t τ hV (sq_nonneg d) hr.2.1 using 1
    dsimp [F3]
    ring
  · rw [hm.2.2]
    convert scaled_residual a4 da4 V d (d^3) t τ hV (pow_nonneg hd 3) hr.2.2 using 1
    dsimp [F4]
    ring

/-- The availability profile misses its ideal decrement -F2 by a bounded
    Taylor remainder. The separate -1 for the chosen vertex is not hidden. -/
theorem availability_residual {V d t τ : ℝ} (hV : 0 < V) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hτ : t+d/V ≤ τ) :
    |Q V (t+d/V)-Q V t+F2 d t| ≤ 30*(1+τ)^4*d^2/V := by
  have hr := q_remainder ht (div_nonneg hd hV.le) hτ
  have he : Q V (t+d/V)-Q V t+F2 d t = V*(q (t+d/V)-q t+a2 t*(d/V)) := by
    dsimp [Q,F2]
    field_simp
  rw [he,abs_mul,abs_of_pos hV]
  calc
    _ ≤ V*(30*(1+τ)^4*(d/V)^2) := mul_le_mul_of_nonneg_left hr hV.le
    _ = _ := by field_simp

/-- Physical profile increments keep the exact powers of q(t). -/
theorem increments {V d t : ℝ} (hV : 0 < V) (hd : 0 ≤ d) (ht : 0 ≤ t) (hstep : d/V ≤ 1) :
    |F2 d (t+d/V)-F2 d t| ≤ 750*(1+t^2)^2*(d^2/V)*q t ∧
    |F3 d (t+d/V)-F3 d t| ≤ 750*(1+t^2)^2*(d^3/V)*(q t)^2 ∧
    |F4 d (t+d/V)-F4 d t| ≤ 750*(1+t^2)^2*(d^4/V)*(q t)^3 := by
  have hh := profile_increment_bounds ht (div_nonneg hd hV.le) hstep
  have scaled (f : ℝ → ℝ) (scale B : ℝ) (hs : 0 ≤ scale)
      (hb : |f (t+d/V)-f t| ≤ B) : |scale*f (t+d/V)-scale*f t| ≤ scale*B := by
    rw [← mul_sub,abs_mul,abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hb hs
  refine ⟨?_,?_,?_⟩
  · convert scaled a2 d _ hd hh.1 using 1
    dsimp [F2]
    ring
  · convert scaled a3 (d^2) _ (sq_nonneg d) hh.2.1 using 1
    dsimp [F3]
    ring
  · convert scaled a4 (d^3) _ (pow_nonneg hd 3) hh.2.2 using 1
    dsimp [F4]
    ring

#print axioms model_scaling
#print axioms residuals
#print axioms availability_residual
#print axioms increments
end
end Erdos773.GreedyScaledTrajectory
