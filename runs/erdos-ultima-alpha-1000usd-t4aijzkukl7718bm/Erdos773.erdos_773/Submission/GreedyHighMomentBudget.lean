import Submission.GreedyPowerYoung

/-!
Fixed even-moment coupled budgets. The constants depend on the moment,
but the time growth remains linear rather than quadratic. No stochastic
trajectory or numerical horizon is asserted in this module.
-/
namespace Erdos773.GreedyHighMomentBudget
open Finset GreedyPowerYoung GreedyWeightedDissipation
set_option maxHeartbeats 2500000

lemma product_le_abs (x y : ℝ) (n : ℕ) : x^n*y ≤ |x|^n*|y| := by
  simpa only [abs_mul,abs_pow] using le_abs_self (x^n*y)

lemma product_sum_bound {α : Type*} (S : Finset α) (x y : α → ℝ) (n : ℕ) :
    (∑ u ∈ S, (x u)^n*y u) ≤ (∑ u ∈ S, |x u|^(n+1))+(∑ u ∈ S, |y u|^(n+1)) := by
  have hp : (0:ℝ) < (n+1:ℕ) := by positivity
  apply le_of_mul_le_mul_left (a := ((n+1:ℕ):ℝ)) ?_ hp
  have hprod := sum_le_sum (fun u (_ : u ∈ S) => product_le_abs (x u) (y u) n)
  have hy := sum_le_sum (s := S) (fun u _ => power_young |x u| |y u| (abs_nonneg _) (abs_nonneg _) n)
  simp only [mul_assoc] at hy
  rw [← mul_sum,sum_add_distrib,← mul_sum] at hy
  have hm := mul_le_mul_of_nonneg_left hprod hp.le
  have hx0 : (0:ℝ) ≤ ∑ u ∈ S, |x u|^(n+1) := by positivity
  have hy0 : (0:ℝ) ≤ ∑ u ∈ S, |y u|^(n+1) := by positivity
  push_cast at hm hy ⊢
  nlinarith only [hm,hy,mul_nonneg (Nat.cast_nonneg n) hy0,hx0]

lemma weighted_product_bound {α : Type*} (S : Finset α) (W : α → α → ℝ) (x y : α → ℝ)
    (hW : ∀ u ∈ S, ∀ v ∈ S, W u v = W v u)
    (hW0 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W u v)
    (B : ℝ) (hB : 0 ≤ B) (hrow : ∀ u ∈ S, (∑ v ∈ S, W u v) ≤ B) (n : ℕ) :
    (∑ u ∈ S, ∑ v ∈ S, W u v*|x u|^n*|y v|) ≤
      B*((∑ u ∈ S, |x u|^(n+1))+(∑ u ∈ S, |y u|^(n+1))) := by
  have hy := weighted_young S W x y hW hW0 B hrow n
  apply le_of_mul_le_mul_left (a := ((n+1:ℕ):ℝ)) ?_ (by positivity)
  apply hy.trans
  have hx0 : (0:ℝ) ≤ ∑ u ∈ S, |x u|^(n+1) := by positivity
  have hy0 : (0:ℝ) ≤ ∑ u ∈ S, |y u|^(n+1) := by positivity
  push_cast
  nlinarith only [mul_nonneg hB hx0,mul_nonneg (mul_nonneg hB (Nat.cast_nonneg n)) hy0]

/-- Absorption of the sole higher-degree coupling whose row bound grows
with t. Its leading 3At^2 coefficient is retained, not inflated. -/
lemma scalar_absorption (n : ℕ) (hn : 1 ≤ n) (A t M N T : ℝ)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hY : 2*(n+1:ℕ)*(t+1)^n*T ≤
      A*(6*t+2)*((n:ℝ)*(t+1)^(n+1)*M+(2:ℝ)^(n+1)*N)) :
    T ≤ A*((3*t^2+4*t+1)*M+6*(2:ℝ)^n*N) := by
  have hpow : t+1 ≤ (t+1)^n := by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ t+1 by linarith) hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hcoeff : 0 ≤ 6*(n+1:ℕ)*(t+1)^n-(6*t+2) := by
    have hm := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ (n+1:ℕ) by exact_mod_cast Nat.succ_pos n)
      (show 0 ≤ (t+1)^n by positivity)
    nlinarith only [hpow,hm]
  have he : 2*(n+1:ℕ)*(t+1)^n*(A*((3*t^2+4*t+1)*M+6*(2:ℝ)^n*N))-
      A*(6*t+2)*((n:ℝ)*(t+1)^(n+1)*M+(2:ℝ)^(n+1)*N) =
      2*(t+1)^n*A*(3*t^2+4*t+1)*M+
        A*(2:ℝ)^(n+1)*(6*(n+1:ℕ)*(t+1)^n-(6*t+2))*N := by
    simp only [Nat.cast_add,Nat.cast_one,pow_succ]
    ring
  have hp : 0 ≤ 2*(t+1)^n*A*(3*t^2+4*t+1)*M+
      A*(2:ℝ)^(n+1)*(6*(n+1:ℕ)*(t+1)^n-(6*t+2))*N := by positivity
  apply le_of_mul_le_mul_left (a := 2*(n+1:ℕ)*(t+1)^n) ?_ (by positivity)
  linarith only [hY,he,hp]

lemma weighted_absorption {α : Type*} (S : Finset α) (W : α → α → ℝ) (x y : α → ℝ)
    (hW : ∀ u ∈ S, ∀ v ∈ S, W u v = W v u)
    (hW0 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W u v) (A t : ℝ) (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hrow : ∀ u ∈ S, (∑ v ∈ S, W u v) ≤ A*(6*t+2)) (n : ℕ) (hn : 1 ≤ n) :
    (∑ u ∈ S, ∑ v ∈ S, W u v*|x u|^n*|y v|) ≤
      A*((3*t^2+4*t+1)*(∑ u ∈ S, |x u|^(n+1))+
        6*(2:ℝ)^n*(∑ u ∈ S, |y u|^(n+1))) := by
  have hh := scaled_weighted_young S W x (fun v => 2*y v) hW hW0
    (A*(6*t+2)) hrow n (t+1) (by positivity)
  simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2),mul_pow] at hh
  have he : (∑ u ∈ S, ∑ v ∈ S, W u v*|x u|^n*(2*|y v|)) =
      2*(∑ u ∈ S, ∑ v ∈ S, W u v*|x u|^n*|y v|) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    rw [mul_sum]
    apply sum_congr rfl
    intro v hv
    ring
  rw [he,← mul_sum] at hh
  apply scalar_absorption n hn A t _ _ _ hA ht (by positivity) (by positivity)
  nlinarith only [hh]

/-- Signed neighbor couplings are bounded by their absolute-product sums. -/
lemma negative_neighbor_bound {α : Type*} (S : Finset α) (W : α → α → ℝ) (x y : α → ℝ)
    (hW0 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W u v) (n : ℕ) :
    (∑ u ∈ S, -(x u)^n*(∑ v ∈ S, W u v*y v)) ≤
      ∑ u ∈ S, ∑ v ∈ S, W u v*|x u|^n*|y v| := by
  apply sum_le_sum
  intro u hu
  rw [mul_sum]
  apply sum_le_sum
  intro v hv
  have hp : -(x u)^n*y v ≤ |x u|^n*|y v| := by
    simpa only [abs_mul,abs_neg,abs_pow] using le_abs_self (-(x u)^n*y v)
  have hh := mul_le_mul_of_nonneg_left hp (hW0 u hu v hv)
  nlinarith only [hh]

/-- Fixed even moments admit a coupled operator bound with growth O(1+t).
No small common-neighbor or promotion error is silently supplied here. -/
theorem coupled_budget {α : Type*} (S : Finset α) (x2 x3 x4 : α → ℝ)
    (W2 W3 W4 : α → α → ℝ) (A t : ℝ) (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hS2 : ∀ u ∈ S, ∀ v ∈ S, W2 u v = W2 v u)
    (hS3 : ∀ u ∈ S, ∀ v ∈ S, W3 u v = W3 v u)
    (hS4 : ∀ u ∈ S, ∀ v ∈ S, W4 u v = W4 v u)
    (hW2 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W2 u v)
    (hW3 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W3 u v)
    (hW4 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W4 u v)
    (hrow3 : ∀ u ∈ S, (∑ v ∈ S, W3 u v) ≤ A*(6*t+2))
    (hrow4 : ∀ u ∈ S, (∑ v ∈ S, W4 u v) ≤ 6*A) (n : ℕ) (hn : Odd n) :
    (∑ u ∈ S, (x2 u)^n*(2*A*x3 u-
      ((∑ v ∈ S, W2 u v)*x2 u+∑ v ∈ S, W2 u v*x2 v)))+
    (∑ u ∈ S, (x3 u)^n*(3*A*x4 u-3*A*t^2*x3 u-∑ v ∈ S, W3 u v*x2 v))+
    (∑ u ∈ S, (x4 u)^n*(-3*A*t^2*x4 u-∑ v ∈ S, W4 u v*x2 v)) ≤
      A*(10+6*(2:ℝ)^n+4*t)*((∑ u ∈ S, |x2 u|^(n+1))+
        (∑ u ∈ S, |x3 u|^(n+1))+(∑ u ∈ S, |x4 u|^(n+1))) := by
  let M2 := ∑ u ∈ S, |x2 u|^(n+1)
  let M3 := ∑ u ∈ S, |x3 u|^(n+1)
  let M4 := ∑ u ∈ S, |x4 u|^(n+1)
  have hM2 : 0 ≤ M2 := by dsimp [M2]; positivity
  have hM3 : 0 ≤ M3 := by dsimp [M3]; positivity
  have hM4 : 0 ≤ M4 := by dsimp [M4]; positivity
  have h23 := mul_le_mul_of_nonneg_left (product_sum_bound S x2 x3 n) (show 0 ≤ 2*A by positivity)
  have h34 := mul_le_mul_of_nonneg_left (product_sum_bound S x3 x4 n) (show 0 ≤ 3*A by positivity)
  have h32 := (negative_neighbor_bound S W3 x3 x2 hW3 n).trans
    (weighted_absorption S W3 x3 x2 hS3 hW3 A t hA ht hrow3 n (by obtain ⟨k,hk⟩ := hn; omega : 1 ≤ n))
  have h42 := (negative_neighbor_bound S W4 x4 x2 hW4 n).trans
    (weighted_product_bound S W4 x4 x2 hS4 hW4 (6*A) (by positivity) hrow4 n)
  have hd := odd_power_nonnegative S W2 x2 hS2 hW2 n hn
  have hpow (x : ℝ) : x^n*x = |x|^(n+1) := by rw [← pow_succ,hn.add_one.pow_abs]
  have he2 : (∑ u ∈ S, (x2 u)^n*(2*A*x3 u-
      ((∑ v ∈ S, W2 u v)*x2 u+∑ v ∈ S, W2 u v*x2 v))) =
      2*A*(∑ u ∈ S, (x2 u)^n*x3 u)-
      (∑ u ∈ S, (x2 u)^n*((∑ v ∈ S, W2 u v)*x2 u+∑ v ∈ S, W2 u v*x2 v)) := by
    rw [mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro u hu
    ring
  have he3 : (∑ u ∈ S, (x3 u)^n*(3*A*x4 u-3*A*t^2*x3 u-∑ v ∈ S, W3 u v*x2 v)) =
      3*A*(∑ u ∈ S, (x3 u)^n*x4 u)-3*A*t^2*M3+
      (∑ u ∈ S, -(x3 u)^n*(∑ v ∈ S, W3 u v*x2 v)) := by
    dsimp only [M3]
    rw [mul_sum,mul_sum,← sum_sub_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro u hu
    rw [← hpow]
    ring
  have he4 : (∑ u ∈ S, (x4 u)^n*(-3*A*t^2*x4 u-∑ v ∈ S, W4 u v*x2 v)) =
      -3*A*t^2*M4+(∑ u ∈ S, -(x4 u)^n*(∑ v ∈ S, W4 u v*x2 v)) := by
    dsimp only [M4]
    rw [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro u hu
    rw [← hpow]
    ring
  have hscalar : 2*A*(M2+M3)+3*A*(M3+M4)+
      A*((3*t^2+4*t+1)*M3+6*(2:ℝ)^n*M2)+6*A*(M4+M2)-3*A*t^2*(M3+M4) ≤
      A*(10+6*(2:ℝ)^n+4*t)*(M2+M3+M4) := by
    have he : A*(10+6*(2:ℝ)^n+4*t)*(M2+M3+M4)-
        (2*A*(M2+M3)+3*A*(M3+M4)+A*((3*t^2+4*t+1)*M3+6*(2:ℝ)^n*M2)+
          6*A*(M4+M2)-3*A*t^2*(M3+M4)) =
        A*((2+4*t)*M2+(4+6*(2:ℝ)^n)*M3+(1+6*(2:ℝ)^n+4*t+3*t^2)*M4) := by ring
    have hp : 0 ≤ A*((2+4*t)*M2+(4+6*(2:ℝ)^n)*M3+(1+6*(2:ℝ)^n+4*t+3*t^2)*M4) := by positivity
    linarith only [he,hp]
  rw [he2,he3,he4]
  change _ ≤ A*(10+6*(2:ℝ)^n+4*t)*(M2+M3+M4)
  change _ ≤ 2*A*(M2+M3) at h23
  change _ ≤ 3*A*(M3+M4) at h34
  change _ ≤ A*((3*t^2+4*t+1)*M3+6*(2:ℝ)^n*M2) at h32
  change _ ≤ 6*A*(M4+M2) at h42
  nlinarith only [h23,h34,h32,h42,hd,hscalar]

#print axioms product_sum_bound
#print axioms weighted_product_bound
#print axioms scalar_absorption
#print axioms weighted_absorption
#print axioms negative_neighbor_bound
#print axioms coupled_budget
end Erdos773.GreedyHighMomentBudget
