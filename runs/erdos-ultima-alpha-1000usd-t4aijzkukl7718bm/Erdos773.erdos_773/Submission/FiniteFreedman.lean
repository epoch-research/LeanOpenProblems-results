import Submission.FiniteKernelCrossing

/-!
A variance-sensitive finite first-crossing bound for adaptive kernels.
This is a concentration tool, not a greedy-process running-time theorem.
-/
namespace Erdos773.FiniteFreedman
open Finset FiniteKernelCrossing
set_option maxHeartbeats 2500000
noncomputable section
variable {σ : Type*} [Fintype σ]

lemma exp_le_quadratic {z : ℝ} (hz : |z| ≤ 1) : Real.exp z ≤ 1+z+z^2 := by
  have hh := Real.norm_exp_sub_one_sub_id_le (x := z) (by simpa only [Real.norm_eq_abs] using hz)
  simp only [Real.norm_eq_abs,sq_abs] at hh
  have hh := (le_abs_self (Real.exp z-1-z)).trans hh
  linarith

/-- A one-step conditional MGF bound using the actual second moment, rather
    than the square of a worst-case bound at every step. -/
theorem one_step_mgf (K : Kernel σ) (d : σ → ℝ) (x : σ) (θ b v : ℝ)
    (hθ : 0 ≤ θ) (hθb : θ*b ≤ 1)
    (hbound : ∀ y, 0 < K.weight x y → |d y| ≤ b)
    (hmean : K.avg d x ≤ 0)
    (hsecond : K.avg (fun y => (d y)^2) x ≤ v) :
    K.avg (fun y => Real.exp (θ*d y)) x ≤ Real.exp (θ^2*v) := by
  have hp (y : σ) (hy : 0 < K.weight x y) :
      Real.exp (θ*d y) ≤ 1+θ*d y+θ^2*(d y)^2 := by
    have hb : |θ*d y| ≤ 1 := by
      rw [abs_mul,abs_of_nonneg hθ]
      exact (mul_le_mul_of_nonneg_left (hbound y hy) hθ).trans hθb
    convert exp_le_quadratic hb using 1; ring
  calc
    _ ≤ K.avg (fun y => 1+θ*d y+θ^2*(d y)^2) x := K.avg_mono_support x hp
    _ = 1+θ*K.avg d x+θ^2*K.avg (fun y => (d y)^2) x := by
      rw [Kernel.avg_add,Kernel.avg_add,Kernel.avg_const,Kernel.avg_mul,Kernel.avg_mul]
    _ ≤ 1+θ^2*v := by
      have hm := mul_nonpos_of_nonneg_of_nonpos hθ hmean
      have hs := mul_le_mul_of_nonneg_left hsecond (sq_nonneg θ)
      linarith
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (θ^2*v)

/-- Exponential potential with accumulated conditional-variance compensation.
    It suffices for V to increase by AT LEAST the second-moment bound on
    every supported transition. -/
theorem compensated_step (K : Kernel σ) (X Y V W : σ → ℝ) (x : σ) (θ b v : ℝ)
    (hθ : 0 ≤ θ) (hθb : θ*b ≤ 1)
    (hbound : ∀ y, 0 < K.weight x y → |Y y-X x| ≤ b)
    (hmean : K.avg (fun y => Y y-X x) x ≤ 0)
    (hsecond : K.avg (fun y => (Y y-X x)^2) x ≤ v)
    (hV : ∀ y, 0 < K.weight x y → V x+v ≤ W y) :
    K.avg (fun y => Real.exp (θ*Y y-θ^2*W y)) x ≤ Real.exp (θ*X x-θ^2*V x) := by
  have hm := one_step_mgf K (fun y => Y y-X x) x θ b v hθ hθb hbound hmean hsecond
  calc
    _ ≤ K.avg (fun y => Real.exp (θ*X x-θ^2*V x-θ^2*v)*Real.exp (θ*(Y y-X x))) x := by
      apply K.avg_mono_support x
      intro y hy
      have hv := mul_le_mul_of_nonneg_left (hV y hy) (sq_nonneg θ)
      have he : θ*Y y-θ^2*W y ≤ (θ*X x-θ^2*V x-θ^2*v)+θ*(Y y-X x) := by nlinarith only [hv]
      exact (Real.exp_le_exp.mpr he).trans_eq (Real.exp_add _ _)
    _ = Real.exp (θ*X x-θ^2*V x-θ^2*v)*
        K.avg (fun y => Real.exp (θ*(Y y-X x))) x := Kernel.avg_mul _ _ _ _
    _ ≤ Real.exp (θ*X x-θ^2*V x-θ^2*v)*Real.exp (θ^2*v) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Crossing the level a while the variance compensator is at most s.
    The crossing event covers every time from 0 through T, inclusive.
    Successive transitions are allowed to depend arbitrarily on the state. -/
theorem first_crossing_exponential (K : ℕ → Kernel σ) (X V : ℕ → σ → ℝ)
    (v : ℕ → σ → ℝ) (T : ℕ) (x₀ : σ) (θ b a s : ℝ)
    (hθ : 0 ≤ θ) (hθb : θ*b ≤ 1) (hX₀ : X 0 x₀ = 0) (hV₀ : V 0 x₀ = 0)
    (hbound : ∀ n < T, ∀ x y, 0 < (K n).weight x y → |X (n+1) y-X n x| ≤ b)
    (hmean : ∀ n < T, ∀ x, (K n).avg (fun y => X (n+1) y-X n x) x ≤ 0)
    (hsecond : ∀ n < T, ∀ x, (K n).avg (fun y => (X (n+1) y-X n x)^2) x ≤ v n x)
    (hV : ∀ n < T, ∀ x y, 0 < (K n).weight x y → V n x+v n x ≤ V (n+1) y) :
    hit K (fun n x => a ≤ X n x ∧ V n x ≤ s) 0 T x₀ ≤ Real.exp (-θ*a+θ^2*s) := by
  let F : ℕ → σ → ℝ := fun n x => Real.exp (θ*X n x-θ^2*V n x)
  let A : ℝ := Real.exp (θ*a-θ^2*s)
  have hA : 0 < A := Real.exp_pos _
  have hstep (n : ℕ) (hn : n < T) (x : σ) : (K n).avg (F (n+1)) x ≤ F n x :=
    compensated_step (K n) (X n) (X (n+1)) (V n) (V (n+1)) x θ b (v n x)
      hθ hθb (hbound n hn x) (hmean n hn x) (hsecond n hn x) (hV n hn x)
  have hdom (n : ℕ) (_hn : n ≤ T) (x : σ) (hx : a ≤ X n x ∧ V n x ≤ s) : A ≤ F n x := by
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left hx.1 hθ
    have h2 := mul_le_mul_of_nonneg_left hx.2 (sq_nonneg θ)
    linarith
  calc
    _ ≤ F 0 x₀/A := hit_le_potential K _ F T A hA
      (fun _ _ _ => (Real.exp_pos _).le) hstep hdom 0 T (by omega) x₀
    _ = _ := by
      dsimp [F,A]
      rw [hX₀,hV₀]
      simp only [mul_zero,sub_self,Real.exp_zero,one_div,← Real.exp_neg]
      congr 1
      ring

/-- A convenient Freedman-type bound, with an explicit constant. The second
    moment control is conditional and the variance budget is tested at the
    crossing time, not merely at the terminal time. -/
theorem first_crossing_bound (K : ℕ → Kernel σ) (X V : ℕ → σ → ℝ)
    (v : ℕ → σ → ℝ) (T : ℕ) (x₀ : σ) (b a s : ℝ)
    (hb : 0 < b) (ha : 0 < a) (hs : 0 ≤ s) (hX₀ : X 0 x₀ = 0) (hV₀ : V 0 x₀ = 0)
    (hbound : ∀ n < T, ∀ x y, 0 < (K n).weight x y → |X (n+1) y-X n x| ≤ b)
    (hmean : ∀ n < T, ∀ x, (K n).avg (fun y => X (n+1) y-X n x) x ≤ 0)
    (hsecond : ∀ n < T, ∀ x, (K n).avg (fun y => (X (n+1) y-X n x)^2) x ≤ v n x)
    (hV : ∀ n < T, ∀ x y, 0 < (K n).weight x y → V n x+v n x ≤ V (n+1) y) :
    hit K (fun n x => a ≤ X n x ∧ V n x ≤ s) 0 T x₀ ≤
      Real.exp (-(a^2)/(4*(s+b*a))) := by
  let S := s+b*a
  have hS : 0 < S := by dsimp [S]; positivity
  let θ := a/(2*S)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθb : θ*b ≤ 1 := by
    change a/(2*S)*b ≤ 1
    rw [div_mul_eq_mul_div]
    apply (div_le_one (by positivity : (0:ℝ) < 2*S)).mpr
    dsimp [S]
    nlinarith only [hs,mul_pos hb ha]
  have hbudget : s ≤ S := by dsimp [S]; nlinarith only [mul_pos hb ha]
  have hexponent : -θ*a+θ^2*s ≤ -(a^2)/(4*S) := by
    calc
      _ ≤ -θ*a+θ^2*S := add_le_add le_rfl (mul_le_mul_of_nonneg_left hbudget (sq_nonneg θ))
      _ = _ := by dsimp [θ]; field_simp; ring
  exact (first_crossing_exponential K X V v T x₀ θ b a s hθ hθb hX₀ hV₀
    hbound hmean hsecond hV).trans (Real.exp_le_exp.mpr hexponent)

/-- Extract a support-respecting path with no low-variance threshold crossing.
    This does not establish a variance budget for any particular application. -/
theorem goodPath_of_variance_control (K : ℕ → Kernel σ) (X V : ℕ → σ → ℝ)
    (v : ℕ → σ → ℝ) (T : ℕ) (x₀ : σ) (b a s : ℝ)
    (hb : 0 < b) (ha : 0 < a) (hs : 0 ≤ s) (hX₀ : X 0 x₀ = 0) (hV₀ : V 0 x₀ = 0)
    (hbound : ∀ n < T, ∀ x y, 0 < (K n).weight x y → |X (n+1) y-X n x| ≤ b)
    (hmean : ∀ n < T, ∀ x, (K n).avg (fun y => X (n+1) y-X n x) x ≤ 0)
    (hsecond : ∀ n < T, ∀ x, (K n).avg (fun y => (X (n+1) y-X n x)^2) x ≤ v n x)
    (hV : ∀ n < T, ∀ x y, 0 < (K n).weight x y → V n x+v n x ≤ V (n+1) y) :
    GoodPath K (fun n x => a ≤ X n x ∧ V n x ≤ s) 0 T x₀ := by
  apply goodPath_of_hit_lt_one
  apply (first_crossing_bound K X V v T x₀ b a s hb ha hs hX₀ hV₀ hbound hmean hsecond hV).trans_lt
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos ha)) (by positivity)

/-- Deterministic variance budget, capped at the horizon for use in the
    crossing event at every time. -/
def budget (v : ℕ → ℝ) (T n : ℕ) : ℝ := ∑ k ∈ range (min n T), v k

lemma budget_le_total (v : ℕ → ℝ) (T n : ℕ) (hv : ∀ k < T, 0 ≤ v k) :
    budget v T n ≤ ∑ k ∈ range T, v k := by
  apply sum_le_sum_of_subset_of_nonneg (range_mono (min_le_right n T))
  intro k hk hkn
  exact hv k (mem_range.mp hk)

lemma budget_step (v : ℕ → ℝ) {T n : ℕ} (hn : n < T) :
    budget v T (n+1) = budget v T n+v n := by
  simp only [budget,min_eq_left (by omega : n+1 ≤ T),min_eq_left hn.le,sum_range_succ]

/-- Deterministic conditional second-moment bounds give an unconditional
    first-crossing estimate, with their sum as the variance budget. -/
theorem first_crossing_deterministic (K : ℕ → Kernel σ) (X : ℕ → σ → ℝ)
    (v : ℕ → ℝ) (T : ℕ) (x₀ : σ) (b a : ℝ) (hb : 0 < b) (ha : 0 < a)
    (hv : ∀ n < T, 0 ≤ v n) (hX₀ : X 0 x₀ = 0)
    (hbound : ∀ n < T, ∀ x y, 0 < (K n).weight x y → |X (n+1) y-X n x| ≤ b)
    (hmean : ∀ n < T, ∀ x, (K n).avg (fun y => X (n+1) y-X n x) x ≤ 0)
    (hsecond : ∀ n < T, ∀ x, (K n).avg (fun y => (X (n+1) y-X n x)^2) x ≤ v n) :
    hit K (fun n x => a ≤ X n x) 0 T x₀ ≤
      Real.exp (-(a^2)/(4*((∑ n ∈ range T, v n)+b*a))) := by
  let V : ℕ → σ → ℝ := fun n _ => budget v T n
  have hV₀ : V 0 x₀ = 0 := by simp [V,budget]
  have hs : 0 ≤ ∑ n ∈ range T, v n := sum_nonneg (fun n hn => hv n (mem_range.mp hn))
  have hV (n : ℕ) (hn : n < T) (x y : σ) (_hy : 0 < (K n).weight x y) :
      V n x+v n ≤ V (n+1) y := by
    dsimp [V]
    rw [budget_step v hn]
  have hpred : (fun n x => a ≤ X n x ∧ V n x ≤ ∑ k ∈ range T, v k) =
      (fun n x => a ≤ X n x) := by
    funext n x
    apply propext
    exact and_iff_left (budget_le_total v T n hv)
  have hh := first_crossing_bound K X V (fun n _ => v n) T x₀ b a _ hb ha hs hX₀ hV₀
    hbound hmean hsecond hV
  rw [hpred] at hh
  exact hh

#print axioms first_crossing_deterministic
#print axioms one_step_mgf
#print axioms compensated_step
#print axioms first_crossing_exponential
#print axioms first_crossing_bound
#print axioms goodPath_of_variance_control
end
end Erdos773.FiniteFreedman
