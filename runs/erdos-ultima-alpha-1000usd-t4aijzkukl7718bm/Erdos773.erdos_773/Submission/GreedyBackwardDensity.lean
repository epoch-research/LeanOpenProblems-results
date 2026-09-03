import Submission.GreedySurvivalTargets

/-!
A finite-step backward target profile. Under explicitly bounded relative
availability errors and closure deficits, the initial target cost depends on
the INITIAL density, rather than the smallest density over the run. No
analytic approximation or presumed greedy trajectory is used.
-/
namespace Erdos773.GreedyBackwardDensity
open Finset GreedyHypergraphState GreedySurvivalTargets
open FiniteKernelCrossing FiniteKilledKernel
set_option maxHeartbeats 2500000
noncomputable section

/-- The exact finite-step cancellation underlying the backward profile. -/
lemma exact_cancellation (w v a B : ℝ) (hw : w ≠ 0) (hv : v ≠ 0) :
    w*(a*(B+1)/w-a*B/v)+(w-v)*(a*B/v) = a := by
  field_simp
  ring

/-- A relative availability error and an absolute closure deficit suffice.
The budget contains the actual time remaining, so no terminal 1/q factor is
introduced into the initial target probability. -/
theorem scalar_step (Q w v l η b a B : ℝ) (hw : 0 < w) (hv : 0 < v)
    (hvw : v ≤ w) (hη : 0 ≤ η) (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hQ : |Q-w| ≤ η*w) (hl : w-v-b ≤ l)
    (hbudget : a*(η*(1+B*(w-v)/v)+b*B/v) ≤ a-1) :
    1 ≤ Q*(a*(B+1)/w-a*B/v)+l*(a*B/v) := by
  let r := a*(B+1)/w
  let s := a*B/v
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hz : 0 ≤ B*(w-v)/v := div_nonneg (mul_nonneg hB (sub_nonneg.mpr hvw)) hv.le
  have hid : r-s = a/w*(1-B*(w-v)/v) := by
    dsimp [r, s]
    field_simp
    ring
  have habs : |r-s| ≤ a/w*(1+B*(w-v)/v) := by
    rw [hid, abs_mul, abs_of_nonneg (div_nonneg ha hw.le)]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg ha hw.le)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have he : |Q-w| * |r-s| ≤ a*η*(1+B*(w-v)/v) := by
    calc
      _ ≤ (η*w)*(a/w*(1+B*(w-v)/v)) :=
        mul_le_mul hQ habs (abs_nonneg _) (mul_nonneg hη hw.le)
      _ = _ := by field_simp
  have hl' := mul_le_mul_of_nonneg_right hl hs
  have hp := neg_abs_le ((Q-w)*(r-s))
  rw [abs_mul] at hp
  have hc : w*(r-s)+(w-v)*s = a := exact_cancellation w v a B hw.ne' hv.ne'
  have heq : a*(η*(1+B*(w-v)/v)+b*B/v) =
      a*η*(1+B*(w-v)/v)+b*s := by dsimp [s]; ring
  rw [heq] at hbudget
  nlinarith only [he, hl', hp, hc, hbudget]

/-- A simple factor-two slack version of the same certificate. -/
theorem scalar_step_two (Q w v l η b B : ℝ) (hw : 0 < w) (hv : 0 < v)
    (hvw : v ≤ w) (hη : 0 ≤ η) (hB : 0 ≤ B)
    (hQ : |Q-w| ≤ η*w) (hl : w-v-b ≤ l)
    (hbudget : η*(1+B*(w-v)/v)+b*B/v ≤ 1/2) :
    1 ≤ Q*(2*(B+1)/w-2*B/v)+l*(2*B/v) := by
  apply scalar_step Q w v l η b 2 B hw hv hvw hη (by norm_num) hB hQ hl
  linarith only [hbudget]

/-- Backward probability parameter with a finite terminal horizon. -/
def parameter (T : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ := 2*(T-n : ℕ)/w n

variable {α σ : Type*} [Fintype α] [DecidableEq α] [Fintype σ]

omit [Fintype σ] in
/-- Construct the actual hazard certificate from finite density error bounds.
The lower closure profile l must pay both its error and the common-neighbor
correction for k simultaneous targets. -/
theorem hazardProfile_of_density (H : Finset (Finset α)) (G : ℕ → σ → Prop)
    (carrier : σ → Finset α) (T k : ℕ) (w η b : ℕ → ℝ)
    (l : ℕ → σ → ℝ) (C : ℕ → σ → ℕ)
    (hw : ∀ n ≤ T, 0 < w n)
    (hwmono : ∀ n < T, w (n+1) ≤ w n)
    (hη : ∀ n < T, 0 ≤ η n)
    (hbudget : ∀ n < T,
      η n*(1+(T-(n+1):ℕ)*(w n-w (n+1))/w (n+1))+
        b n*(T-(n+1):ℕ)/w (n+1) ≤ 1/2)
    (hlocal : ∀ n < T, ∀ x, G n x →
      |(available H (carrier x)).card-w n| ≤ η n*w n ∧
      w n-w (n+1)-b n ≤ l n x-((k:ℝ)-1)/2*C n x ∧
      (∀ u ∈ available H (carrier x), l n x ≤ (closes H (carrier x) u).card) ∧
      (∀ u ∈ available H (carrier x), ∀ v ∈ available H (carrier x), u ≠ v →
        (closes H (carrier x) u ∩ closes H (carrier x) v).card ≤ C n x)) :
    HazardProfile H G carrier T k (parameter T w) l C := by
  constructor
  · intro n hn
    exact div_nonneg (by positivity) (hw n hn).le
  · intro n hn x hx
    obtain ⟨hQ, hl, hdeg, hC⟩ := hlocal n hn x hx
    refine ⟨hdeg, hC, ?_⟩
    have hstep := scalar_step_two (available H (carrier x)).card (w n) (w (n+1))
      (l n x-((k:ℝ)-1)/2*C n x) (η n) (b n) (T-(n+1):ℕ)
      (hw n (by omega)) (hw (n+1) (by omega)) (hwmono n hn) (hη n hn)
      (by positivity) hQ hl (hbudget n hn)
    have htime : T-n = (T-(n+1))+1 := by omega
    simpa only [parameter, htime, Nat.cast_add, Nat.cast_one] using hstep

#print axioms exact_cancellation
#print axioms scalar_step
#print axioms scalar_step_two
#print axioms hazardProfile_of_density
end
end Erdos773.GreedyBackwardDensity
