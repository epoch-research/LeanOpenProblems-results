import Submission.IntegerFourDensityIncrement

/-! A quantitative finite four-term theorem obtained by iterating the
interval-relative density increment. No reciprocal-summability claim is made. -/
namespace Erdos3IntegerFourDensityBound
open Finset Erdos3IntegerFourDensityIncrement Erdos3CyclicIntervalMask
open scoped Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

noncomputable def fourIterationThreshold (α : ℝ) : ℕ → ℕ
  | 0 => 1
  | t+1 => intervalStepThreshold α (fourIterationThreshold α t)
noncomputable def fourIterationCount (α : ℝ) : ℕ := ⌈32/intervalGain α⌉₊+1
noncomputable def fourIntervalBound (α : ℝ) : ℕ := fourIterationThreshold α (fourIterationCount α)

lemma fourIterationThreshold_pos (α : ℝ) (t : ℕ) : 0 < fourIterationThreshold α t := by
  cases t with
  | zero => exact Nat.zero_lt_one
  | succ t =>
    change 0 < intervalStepThreshold α (fourIterationThreshold α t)
    exact lt_of_lt_of_le (by decide : 0 < 8) (le_max_left _ _)

lemma fourIterationCount_gain {α : ℝ} (hα : 0 < α) :
    1 < (fourIterationCount α : ℝ)*(intervalGain α/32) := by
  have hr := intervalGain_pos hα
  have hh : 32/intervalGain α < (fourIterationCount α : ℝ) := by
    apply (Nat.le_ceil _).trans_lt
    simp only [fourIterationCount,Nat.cast_add,Nat.cast_one]
    linarith
  have hp := (div_lt_iff₀ hr).mp hh
  nlinarith only [hp]

/-- Each possible increment consumes a fixed positive amount of density.
The ambient interval size hypotheses are supplied by a finite threshold recursion. -/
theorem iterated_density_upper {α : ℝ} (hα : 0 < α) (t : ℕ) :
    ∀ N : ℕ, ∀ S : Finset ℕ, S ⊆ range N → (S : Set ℕ).IsAPOfLengthFree 4 →
      α ≤ intervalDensity S N → fourIterationThreshold α t ≤ N →
      intervalDensity S N+(t : ℝ)*(intervalGain α/32) ≤ 1 := by
  induction t with
  | zero =>
    intro N S hS hfree hden hN
    have hN0 : 0 < N := (fourIterationThreshold_pos α 0).trans_le hN
    simpa only [Nat.cast_zero,zero_mul,add_zero] using (intervalDensity_bounds N hN0 S hS).2
  | succ t ih =>
    intro N S hS hfree hden hN
    obtain ⟨m,T,hm,hml,_,hT,hTf,hinc⟩ := integer_four_density_increment hα N
      (fourIterationThreshold α t) hN S hS hfree hden
    have hr : 0 < intervalGain α/32 := div_pos (intervalGain_pos hα) (by norm_num)
    have hden' : α ≤ intervalDensity T m := hden.trans ((le_add_of_nonneg_right hr.le).trans hinc)
    have hh := ih m T hT hTf hden' hml
    rw [Nat.cast_succ]
    nlinarith only [hh,hinc]

/-- Above the explicit bound, an integer interval cannot contain a four-term-
free subset with density at least alpha. This is a complete finite four-term
density bound, but its costs have not been shown to give reciprocal summability. -/
theorem integer_four_density_bound {α : ℝ} (hα : 0 < α) (N : ℕ) (S : Finset ℕ)
    (hS : S ⊆ range N) (hfree : (S : Set ℕ).IsAPOfLengthFree 4)
    (hden : α ≤ intervalDensity S N) : N < fourIntervalBound α := by
  by_contra! hN
  have hh := iterated_density_upper hα (fourIterationCount α) N S hS hfree hden hN
  have hg := fourIterationCount_gain hα
  linarith

#print axioms iterated_density_upper
#print axioms integer_four_density_bound
end Erdos3IntegerFourDensityBound
