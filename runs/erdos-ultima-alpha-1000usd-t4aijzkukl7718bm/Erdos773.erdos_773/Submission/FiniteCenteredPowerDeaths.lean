import Submission.FiniteCenteredPower
import Submission.GreedySurvivalTotalDrift

/-!
Optimally centered power drift retaining the energy at killed coordinates.
The discarded death term in a weaker upper bound is restored explicitly.
-/
namespace Erdos773.FiniteCenteredPowerDeaths
open Finset FiniteCenteredPower
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

/-- Evaluate the next minimum at any center and retain all killed old mass. -/
theorem survivor_step {S T : Finset α} (hTS : T ⊆ S) (f g : α → ℝ) (p : ℕ) (a : ℝ) :
    energy T g p-energy S f p ≤
      (∑ u ∈ T, (|g u-a|^p-|f u-center S f p|^p))-
      (∑ u ∈ S \ T, |f u-center S f p|^p) := by
  have hnew := energy_le T g p a
  have hold : (∑ u ∈ T, |f u-center S f p|^p)+
      (∑ u ∈ S \ T, |f u-center S f p|^p) = energy S f p := by
    exact (add_comm _ _).trans (sum_sdiff hTS)
  rw [sum_sub_distrib]
  change energy T g p ≤ ∑ u ∈ T, |g u-a|^p at hnew
  linarith only [hnew, hold]

/-- Taylor estimate with the full negative death-energy term. -/
theorem survivor_taylor {S T : Finset α} (hTS : T ⊆ S) (f g : α → ℝ)
    (n : ℕ) (hn : Even (n+2)) (a : ℝ) (B : α → ℝ)
    (hB : ∀ u ∈ T, |(g u-a)-(f u-center S f (n+2))| ≤ B u) :
    energy T g (n+2)-energy S f (n+2) ≤
      (∑ u ∈ T, ((n+2:ℕ)*(f u-center S f (n+2))^(n+1)*
        ((g u-a)-(f u-center S f (n+2)))+
        FinitePowerTaylor.coefficient n*(|f u-center S f (n+2)|^n+(B u)^n)*
          ((g u-a)-(f u-center S f (n+2)))^2))-
      (∑ u ∈ S \ T, |f u-center S f (n+2)|^(n+2)) := by
  apply (survivor_step hTS f g (n+2) a).trans
  apply sub_le_sub_right
  apply sum_le_sum
  intro u hu
  have hh := (abs_le.mp (FinitePowerTaylor.bounded_remainder
    (f u-center S f (n+2)) ((g u-a)-(f u-center S f (n+2))) (B u) n (hB u hu))).2
  rw [add_sub_cancel] at hh
  rw [hn.pow_abs, hn.pow_abs]
  linarith only [hh]

/-- Double-count old mass at all killed coordinates. -/
lemma death_sum (S : Finset α) (T : α → Finset α) (hT : ∀ v ∈ S, T v ⊆ S)
    (f : α → ℝ) :
    (∑ v ∈ S, ∑ u ∈ S \ T v, f u) =
      ∑ u ∈ S, ((S.card:ℝ)-(S.filter (fun v => u ∈ T v)).card)*f u := by
  have he (v : α) (hv : v ∈ S) :
      (∑ u ∈ S \ T v, f u) = (∑ u ∈ S, f u)-(∑ u ∈ T v, f u) := by
    exact sum_sdiff_eq_sub (hT v hv)
  rw [sum_congr rfl he, sum_sub_distrib, sum_const, nsmul_eq_mul,
    GreedySurvivalTotalDrift.survivor_sum S T hT]
  simp_rw [sum_const, nsmul_eq_mul, sub_mul]
  rw [sum_sub_distrib, mul_sum]

#print axioms survivor_step
#print axioms survivor_taylor
#print axioms death_sum
end
end Erdos773.FiniteCenteredPowerDeaths
