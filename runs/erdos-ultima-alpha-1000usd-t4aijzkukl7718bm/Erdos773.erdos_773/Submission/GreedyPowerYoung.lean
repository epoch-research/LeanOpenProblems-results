import Submission.GreedyWeightedDissipation

/-!
Natural-power Young inequalities for symmetric neighbor operators. The
exponent can be any fixed natural number, which avoids relying solely on
a global quadratic moment when controlling many local degree records.
-/
namespace Erdos773.GreedyPowerYoung
open Finset
set_option maxHeartbeats 2500000

/-- Integer-power Young inequality, proved by a polynomial recurrence. -/
theorem power_young (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (n+1:ℕ)*a^n*b ≤ (n:ℝ)*a^(n+1)+b^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmul := mul_le_mul_of_nonneg_left ih hb
    have hp : 0 ≤ (n+1:ℕ)*a^n*(a-b)^2 := by positivity
    have he : ((n+1:ℕ)*a^(n+2)+b^(n+2))-((n+2:ℕ)*a^(n+1)*b) =
        b*((n:ℝ)*a^(n+1)+b^(n+1)-(n+1:ℕ)*a^n*b)+
          (n+1:ℕ)*a^n*(a-b)^2 := by
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,pow_succ]
      ring
    change (n+2:ℕ)*a^(n+1)*b ≤ (n+1:ℕ)*a^(n+2)+b^(n+2)
    nlinarith only [hmul,hp,he]

/-- The weighted Young inequality uses row bounds twice, with symmetry
providing the column bound needed for the second component. -/
theorem weighted_young {α : Type*} (S : Finset α) (W : α → α → ℝ) (f g : α → ℝ)
    (hW : ∀ u ∈ S, ∀ v ∈ S, W u v = W v u)
    (hW0 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W u v)
    (B : ℝ) (hrow : ∀ u ∈ S, (∑ v ∈ S, W u v) ≤ B) (n : ℕ) :
    (n+1:ℕ)*(∑ u ∈ S, ∑ v ∈ S, W u v*|f u|^n*|g v|) ≤
      B*((n:ℝ)*(∑ u ∈ S, |f u|^(n+1))+(∑ u ∈ S, |g u|^(n+1))) := by
  have hp (u : α) (hu : u ∈ S) (v : α) (hv : v ∈ S) :
      (n+1:ℕ)*(W u v*|f u|^n*|g v|) ≤ W u v*((n:ℝ)*|f u|^(n+1)+|g v|^(n+1)) := by
    have hh := mul_le_mul_of_nonneg_left (power_young |f u| |g v| (abs_nonneg _) (abs_nonneg _) n)
      (hW0 u hu v hv)
    nlinarith only [hh]
  have hs := sum_le_sum (fun u hu => sum_le_sum (fun v hv => hp u hu v hv))
  simp only [← mul_sum] at hs
  have he : (∑ u ∈ S, ∑ v ∈ S, W u v*((n:ℝ)*|f u|^(n+1)+|g v|^(n+1))) =
      (∑ u ∈ S, (∑ v ∈ S, W u v)*((n:ℝ)*|f u|^(n+1)))+
      (∑ u ∈ S, (∑ v ∈ S, W u v)*|g u|^(n+1)) := by
    simp_rw [mul_add,sum_add_distrib]
    congr 1
    · apply sum_congr rfl
      intro u hu
      rw [← sum_mul]
    · rw [sum_comm]
      apply sum_congr rfl
      intro u hu
      rw [← sum_mul]
      congr 1
      apply sum_congr rfl
      intro v hv
      exact hW v hv u hu
  rw [he] at hs
  apply hs.trans
  have hf := sum_le_sum (fun u hu => mul_le_mul_of_nonneg_right (hrow u hu)
    (show 0 ≤ (n:ℝ)*|f u|^(n+1) by positivity))
  have hg := sum_le_sum (fun u hu => mul_le_mul_of_nonneg_right (hrow u hu)
    (show 0 ≤ |g u|^(n+1) by positivity))
  simpa only [← mul_sum,mul_add,mul_assoc] using add_le_add hf hg

/-- Scaling one component allows its restoring drift to absorb a neighbor
coupling without making its leading t^2 term a positive growth rate. -/
theorem scaled_weighted_young {α : Type*} (S : Finset α) (W : α → α → ℝ) (f g : α → ℝ)
    (hW : ∀ u ∈ S, ∀ v ∈ S, W u v = W v u)
    (hW0 : ∀ u ∈ S, ∀ v ∈ S, 0 ≤ W u v)
    (B : ℝ) (hrow : ∀ u ∈ S, (∑ v ∈ S, W u v) ≤ B) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (n+1:ℕ)*t^n*(∑ u ∈ S, ∑ v ∈ S, W u v*|f u|^n*|g v|) ≤
      B*((n:ℝ)*t^(n+1)*(∑ u ∈ S, |f u|^(n+1))+(∑ u ∈ S, |g u|^(n+1))) := by
  have hh := weighted_young S W (fun u => t*f u) g hW hW0 B hrow n
  simp only [abs_mul,abs_of_nonneg ht,mul_pow] at hh
  have he : (∑ u ∈ S, ∑ v ∈ S, W u v*(t^n*|f u|^n)*|g v|) =
      t^n*(∑ u ∈ S, ∑ v ∈ S, W u v*|f u|^n*|g v|) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    rw [mul_sum]
    apply sum_congr rfl
    intro v hv
    ring
  rw [he,← mul_sum] at hh
  simpa only [mul_assoc] using hh

#print axioms power_young
#print axioms weighted_young
#print axioms scaled_weighted_young
end Erdos773.GreedyPowerYoung
