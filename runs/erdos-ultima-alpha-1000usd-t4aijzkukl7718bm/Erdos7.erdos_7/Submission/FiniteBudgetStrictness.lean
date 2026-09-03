import Submission.FiniteGeometricBudget

/-! Strictness in a finite geometric cutoff requires nonconstant tests.
These auxiliary facts do not exclude an odd covering system. -/
namespace Erdos7FiniteBudgetStrictness
open scoped BigOperators
open Erdos7FiniteGeometricBudget
set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma op_constant (p c h a : ℝ) (E : ℕ) (x : ℝ) :
    op p c h (fun _ => a) E x = h*a := by
  simp [op]

lemma budget_constant (p c h a : ℝ) (E : ℕ) (x : ℝ) :
    budget p c h (fun _ => a) 0 E x = h*a := by
  simp [budget, op_constant]

/-- Finite truncation is an equality for the constant root potential, at
 every exponent cap; finiteness alone cannot turn this bound into `< 1`. -/
lemma constant_root_equality (p c : ℝ) (E R : ℕ) (x : ℝ) :
    op p c 1 (fun _ => (1 : ℝ)) E x =
      budget p c 1 (fun _ => (1 : ℝ)) 0 R x ∧
    op p c 1 (fun _ => (1 : ℝ)) E x = 1 := by
  simp [op_constant, budget_constant]

lemma positive_tail_strict (u T : ℕ → ℝ) (N : ℕ)
    (hu : ∀ j, 0 ≤ u j) (hT : ∀ j, 0 < T j)
    (hstep : ∀ j, N ≤ j → u j + T (j+1) ≤ T j) (E : ℕ) :
    (∑ j ∈ Finset.range E, u j) < (∑ j ∈ Finset.range N, u j) + T N := by
  by_cases hEN : E ≤ N
  · have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hEN)
      (fun j _ _ => hu j)
    linarith [hT N]
  · have hNE : N ≤ E := by omega
    have hbound : ∀ k, N ≤ k → (∑ j ∈ Finset.range k, u j) + T k ≤
        (∑ j ∈ Finset.range N, u j) + T N := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact le_rfl
      | succ k hk ih =>
        rw [Finset.sum_range_succ]
        linarith [hstep k hk]
    linarith [hbound E hNE, hT E]

/-- A positive affine-tail slope does give strictness for every finite cap.
The sign assumptions are substantive: a constant test has slope zero. -/
theorem op_lt_budget_of_positive_slope (p c h : ℝ) (hp : 1 < p)
    (hc : 0 < c) (hh : 0 ≤ h) (f : ℝ → ℝ) (hmf : Monotone f)
    (T S : ℝ) (hS : 0 < S)
    (hf : ∀ y, T ≤ y → f y = f T + S*(y-T))
    (N E : ℕ) (x : ℝ) (hx : 0 < x) (hTx : T ≤ (N+1)*x) :
    op p c h f E x < budget p c h f S N x := by
  have hjT (j : ℕ) (hj : N ≤ j) : T ≤ (j+1)*x := by
    have hcast : (N : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have hinc0 (j : ℕ) : 0 ≤ f ((j+2)*x)-f ((j+1)*x) := by
    exact sub_nonneg.mpr (hmf (by nlinarith))
  have htail (j : ℕ) : 0 < tail p c j*S*x := by
    have hpos : 0 < tail p c j := by
      unfold tail
      exact div_pos hc (mul_pos (pow_pos (by linarith) _) (by linarith))
    exact mul_pos (mul_pos hpos hS) hx
  have hbound := positive_tail_strict
    (fun j => q p c h j*(f ((j+2)*x)-f ((j+1)*x)))
    (fun j => tail p c j*S*x) N
    (fun j => mul_nonneg (q_nonneg p c h hp hc.le hh j) (hinc0 j)) htail
    (fun j hj => by
      dsimp only
      rw [affine_increment f T S hf x hx.le j (hjT j hj)]
      have hq := mul_le_mul_of_nonneg_right (min_le_right h (c/p^(j+1)))
        (mul_nonneg hS.le hx.le)
      have ht := congrArg (fun z : ℝ => z*S*x) (tail_step p c hp j)
      dsimp only [q]
      nlinarith) E
  dsimp only [op, budget]
  linarith

#print axioms constant_root_equality
#print axioms op_lt_budget_of_positive_slope
end Erdos7FiniteBudgetStrictness
