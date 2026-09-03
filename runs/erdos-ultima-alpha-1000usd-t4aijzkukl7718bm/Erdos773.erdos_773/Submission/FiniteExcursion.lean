import Submission.FiniteFreedman

/-!
A finite first-crossing estimate for critical excursions. The conditional
mean and second-moment assumptions are required only at states where the
observable is nonnegative. The factor T+1 accounts for possible entrances
from below zero; no independence or fixed entrance time is assumed.
-/
namespace Erdos773.FiniteExcursion
open Finset FiniteKernelCrossing FiniteFreedman
set_option maxHeartbeats 2500000
noncomputable section
variable {σ : Type*} [Fintype σ]

/-- One possible new excursion per step costs at most exp(θ*b). -/
lemma excursion_step (K : Kernel σ) (X Y : σ → ℝ) (x : σ)
    (θ b v V : ℝ) (hθ : 0 ≤ θ) (hv : 0 ≤ v) (hV : 0 ≤ V)
    (hθb : θ*b ≤ 1)
    (hbound : ∀ y, 0 < K.weight x y → |Y y-X x| ≤ b)
    (hmean : 0 ≤ X x → K.avg (fun y => Y y-X x) x ≤ 0)
    (hsecond : 0 ≤ X x → K.avg (fun y => (Y y-X x)^2) x ≤ v) :
    K.avg (fun y => Real.exp (θ*Y y-θ^2*(V+v))) x ≤
      Real.exp (θ*X x-θ^2*V)+Real.exp (θ*b) := by
  by_cases hx : 0 ≤ X x
  · exact (compensated_step K X Y (fun _ => V) (fun _ => V+v) x θ b v hθ hθb
      hbound (hmean hx) (hsecond hx) (fun _ _ => le_rfl)).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hpoint (y : σ) (hy : 0 < K.weight x y) :
        Real.exp (θ*Y y-θ^2*(V+v)) ≤ Real.exp (θ*b) := by
      have hyb := (le_abs_self (Y y-X x)).trans (hbound y hy)
      have hyb : Y y ≤ b := by linarith
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hyb hθ
      have hn := mul_nonneg (sq_nonneg θ) (add_nonneg hV hv)
      linarith
    have hh := K.avg_mono_support x hpoint
    rw [Kernel.avg_const] at hh
    exact hh.trans (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- Critical-excursion first-crossing bound in exponential-parameter form.
    All crossings in 0..T are included. -/
theorem first_crossing_exponential (K : ℕ → Kernel σ) (X : ℕ → σ → ℝ)
    (v : ℕ → ℝ) (T : ℕ) (x₀ : σ) (θ b a : ℝ)
    (hθ : 0 ≤ θ) (hb : 0 ≤ b) (hθb : θ*b ≤ 1)
    (hv : ∀ n < T, 0 ≤ v n) (hX₀ : X 0 x₀ ≤ 0)
    (hbound : ∀ n < T, ∀ x y, 0 < (K n).weight x y → |X (n+1) y-X n x| ≤ b)
    (hmean : ∀ n < T, ∀ x, 0 ≤ X n x → (K n).avg (fun y => X (n+1) y-X n x) x ≤ 0)
    (hsecond : ∀ n < T, ∀ x, 0 ≤ X n x →
      (K n).avg (fun y => (X (n+1) y-X n x)^2) x ≤ v n) :
    hit K (fun n x => a ≤ X n x) 0 T x₀ ≤
      ((T:ℝ)+1)*Real.exp (-θ*(a-b)+θ^2*(∑ n ∈ range T, v n)) := by
  let V : ℕ → ℝ := budget v T
  let F : ℕ → σ → ℝ := fun n x =>
    Real.exp (θ*X n x-θ^2*V n)+(T-n:ℕ)*Real.exp (θ*b)
  let S : ℝ := ∑ n ∈ range T, v n
  let A : ℝ := Real.exp (θ*a-θ^2*S)
  have hA : 0 < A := Real.exp_pos _
  have hV (n : ℕ) : 0 ≤ V n := by
    apply sum_nonneg
    intro k hk
    exact hv k (lt_of_lt_of_le (mem_range.mp hk) (min_le_right n T))
  have hstep (n : ℕ) (hn : n < T) (x : σ) : (K n).avg (F (n+1)) x ≤ F n x := by
    have hh := excursion_step (K n) (X n) (X (n+1)) x θ b (v n) (V n)
      hθ (hv n hn) (hV n) hθb (hbound n hn x) (hmean n hn x) (hsecond n hn x)
    have htime : ((T-n:ℕ):ℝ) = ((T-(n+1):ℕ):ℝ)+1 := by
      have ht : T-n = (T-(n+1))+1 := by omega
      exact_mod_cast ht
    dsimp [F]
    rw [Kernel.avg_add,Kernel.avg_const]
    have hvstep : V (n+1) = V n+v n := budget_step v hn
    rw [hvstep,htime]
    nlinarith only [hh]
  have hdom (n : ℕ) (hn : n ≤ T) (x : σ) (hx : a ≤ X n x) : A ≤ F n x := by
    have hh : A ≤ Real.exp (θ*X n x-θ^2*V n) := by
      apply Real.exp_le_exp.mpr
      have hh1 := mul_le_mul_of_nonneg_left hx hθ
      have hh2 := mul_le_mul_of_nonneg_left (budget_le_total v T n hv) (sq_nonneg θ)
      dsimp [V,S] at *
      linarith
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  have hh := hit_le_potential K _ F T A hA
    (fun _ _ _ => by dsimp [F]; positivity) hstep hdom 0 T (by omega) x₀
  apply hh.trans
  have hstart : F 0 x₀ ≤ ((T:ℝ)+1)*Real.exp (θ*b) := by
    have he : Real.exp (θ*X 0 x₀) ≤ Real.exp (θ*b) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (hX₀.trans hb) hθ
    simp only [F,V,budget,Nat.zero_min,range_zero,sum_empty,mul_zero,sub_zero,Nat.sub_zero]
    nlinarith only [he]
  calc
    _ ≤ (((T:ℝ)+1)*Real.exp (θ*b))/A := div_le_div_of_nonneg_right hstart hA.le
    _ = _ := by
      rw [mul_div_assoc]
      congr 1
      dsimp [A]
      rw [← Real.exp_sub]
      congr 1
      ring

/-- Optimized critical-excursion estimate. The gap is a-b because an entrance
    from below zero can overshoot zero by one bounded increment. -/
theorem first_crossing_bound (K : ℕ → Kernel σ) (X : ℕ → σ → ℝ)
    (v : ℕ → ℝ) (T : ℕ) (x₀ : σ) (b a : ℝ)
    (hb : 0 < b) (ha : b < a)
    (hv : ∀ n < T, 0 ≤ v n) (hX₀ : X 0 x₀ ≤ 0)
    (hbound : ∀ n < T, ∀ x y, 0 < (K n).weight x y → |X (n+1) y-X n x| ≤ b)
    (hmean : ∀ n < T, ∀ x, 0 ≤ X n x → (K n).avg (fun y => X (n+1) y-X n x) x ≤ 0)
    (hsecond : ∀ n < T, ∀ x, 0 ≤ X n x →
      (K n).avg (fun y => (X (n+1) y-X n x)^2) x ≤ v n) :
    hit K (fun n x => a ≤ X n x) 0 T x₀ ≤
      ((T:ℝ)+1)*Real.exp (-((a-b)^2)/(4*((∑ n ∈ range T, v n)+b*(a-b)))) := by
  let s : ℝ := ∑ n ∈ range T, v n
  let S : ℝ := s+b*(a-b)
  let θ : ℝ := (a-b)/(2*S)
  have hab : 0 < a-b := sub_pos.mpr ha
  have hs : 0 ≤ s := sum_nonneg (fun n hn => hv n (mem_range.mp hn))
  have hS : 0 < S := by dsimp [S]; positivity
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθb : θ*b ≤ 1 := by
    dsimp [θ]
    rw [div_mul_eq_mul_div]
    apply (div_le_one (by positivity : (0:ℝ) < 2*S)).mpr
    dsimp [S]
    nlinarith only [hs,mul_pos hb hab]
  have hbudget : s ≤ S := by dsimp [S]; nlinarith only [mul_pos hb hab]
  have he : -θ*(a-b)+θ^2*s ≤ -((a-b)^2)/(4*S) := by
    calc
      _ ≤ -θ*(a-b)+θ^2*S := add_le_add le_rfl (mul_le_mul_of_nonneg_left hbudget (sq_nonneg θ))
      _ = _ := by dsimp [θ]; field_simp; ring
  apply (first_crossing_exponential K X v T x₀ θ b a hθ hb.le hθb hv hX₀ hbound hmean hsecond).trans
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)

#print axioms excursion_step
#print axioms first_crossing_exponential
#print axioms first_crossing_bound
end
end Erdos773.FiniteExcursion
