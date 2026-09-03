import Submission.BudgetedStrongRegularity

/-! A summable allocation of localization tolerances across adaptive stages.
The choice uses only the current detector gain and the prescribed total error,
not the eventual number of stages or the final coarse complexity. -/
namespace Erdos3SummableStageBudgets
open Finset Erdos3AdaptiveStrongRegularity Erdos3BudgetedStrongRegularity
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

noncomputable def unitBlockSize (ρ : ℕ → NNReal) (j : ℕ) : ℕ := ⌈1/(ρ j : ℝ)^2⌉₊+1

noncomputable def stageTolerance (ρ : ℕ → NNReal) (τ : ℝ) (j : ℕ) : ℕ :=
  ⌈(2 : ℝ)^(j+2)*(unitBlockSize ρ j : ℝ)*(ρ j : ℝ)/τ⌉₊+1

lemma stageTolerance_pos (ρ : ℕ → NNReal) (τ : ℝ) (j : ℕ) : 0 < stageTolerance ρ τ j := by
  unfold stageTolerance
  omega

lemma stage_cost_bound (ρ : ℕ → NNReal) {τ : ℝ} (hτ : 0 < τ) (j : ℕ) :
    (unitBlockSize ρ j : ℝ)*(ρ j : ℝ)/(stageTolerance ρ τ j : ℝ) ≤ τ/(2 : ℝ)^(j+2) := by
  have hz : (0 : ℝ) < stageTolerance ρ τ j := by exact_mod_cast stageTolerance_pos ρ τ j
  have hp : (0 : ℝ) < (2 : ℝ)^(j+2) := by positivity
  have hc : (2 : ℝ)^(j+2)*(unitBlockSize ρ j : ℝ)*(ρ j : ℝ)/τ ≤
      (stageTolerance ρ τ j : ℝ) := by
    apply (Nat.le_ceil _).trans
    unfold stageTolerance
    rw [Nat.cast_add,Nat.cast_one]
    linarith
  have hh := (div_le_iff₀ hτ).mp hc
  apply (div_le_div_iff₀ hz hp).mpr
  nlinarith only [hh]

lemma sum_dyadic_tail (m : ℕ) :
    (∑ j ∈ range m, (1/2 : ℝ)^(j+2)) = 1/2-(1/2 : ℝ)^(m+1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ,ih]
    simp only [pow_succ]
    ring

lemma sum_dyadic_tail_le (m : ℕ) : (∑ j ∈ range m, (1/2 : ℝ)^(j+2)) ≤ 1/2 := by
  rw [sum_dyadic_tail]
  have hp : 0 ≤ (1/2 : ℝ)^(m+1) := by positivity
  linarith

variable {X : Type*} [Fintype X] [Nonempty X]

lemma blockSize_le_unit (f : X → ℝ) (hf : ∀ x, f x ≤ 1) (ρ : ℕ → NNReal) (j : ℕ) :
    blockSize f ρ j ≤ unitBlockSize ρ j := by
  unfold blockSize unitBlockSize
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right (expect_le univ_nonempty (fun x _ ↦ hf x)) (sq_nonneg _)

/-- Every prefix of stages spends at most half the prescribed local L2 error
budget on the weighted stability errors. -/
theorem prefix_stage_budget (f : X → ℝ) (hf : ∀ x, f x ≤ 1) (ρ : ℕ → NNReal)
    {τ : ℝ} (hτ : 0 < τ) (m : ℕ) :
    prefixCost (blockSize f ρ) (fun j ↦ (ρ j : ℝ)/(stageTolerance ρ τ j : ℝ)) m ≤ τ/2 := by
  unfold prefixCost
  calc
    _ ≤ ∑ j ∈ range m, τ*(1/2 : ℝ)^(j+2) := by
      apply sum_le_sum
      intro j _
      have hb : (blockSize f ρ j : ℝ) ≤ unitBlockSize ρ j := by exact_mod_cast blockSize_le_unit f hf ρ j
      calc
        _ ≤ (unitBlockSize ρ j : ℝ)*((ρ j : ℝ)/(stageTolerance ρ τ j : ℝ)) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
        _ = (unitBlockSize ρ j : ℝ)*(ρ j : ℝ)/(stageTolerance ρ τ j : ℝ) := by ring
        _ ≤ τ/(2 : ℝ)^(j+2) := stage_cost_bound ρ hτ j
        _ = _ := by rw [one_div_pow]; ring
    _ = τ*(∑ j ∈ range m, (1/2 : ℝ)^(j+2)) := (mul_sum ..).symm
    _ ≤ τ*(1/2) := mul_le_mul_of_nonneg_left (sum_dyadic_tail_le m) hτ.le
    _ = _ := by ring

#print axioms stage_cost_bound
#print axioms prefix_stage_budget
end Erdos3SummableStageBudgets
