import Submission.ConsecutiveRatioFibres
import Submission.DivisorSubpower

/-! Uniform subpower completion bounds for the exact product-equality
configurations of `ConsecutiveRatioFibres`. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

def balancedFourCompletionCount (a b N : ℕ) : ℕ :=
  (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z : ℕ × ℕ =>
    (a+1)*(b+1)*z.1*z.2=a*b*(z.1+1)*(z.2+1)).card

def alternatingFourCompletionCount (a b N : ℕ) : ℕ :=
  (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z : ℕ × ℕ =>
    (a+1)*b*(z.1+1)*z.2=a*(b+1)*z.1*(z.2+1)).card

def threeForwardCompletionCount (a b N : ℕ) : ℕ :=
  (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z : ℕ × ℕ =>
    (a+1)*(b+1)*(z.1+1)*z.2=a*b*z.1*(z.2+1)).card

lemma four_ratio_divisor_argument_le (a b N : ℕ) (hN : 2 ≤ N)
    (ha : a ≤ N) (hb : b ≤ N) : a*b*(a+1)*(b+1) ≤ N^8 := by
  have hN2 : N ≤ N^2 := by nlinarith
  have ha1 : a+1 ≤ N^2 := by nlinarith
  have hb1 : b+1 ≤ N^2 := by nlinarith
  calc
    _ ≤ N^2*N^2*N^2*N^2 := by
      exact Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.mul_le_mul (ha.trans hN2) (hb.trans hN2)) ha1) hb1
    _ = _ := by ring

/-- Uniformly in both prescribed entries. The alternating diagonal is
excluded here because its completion count is exactly N. -/
theorem four_ratio_completion_uniform_subpower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N,
      (balancedFourCompletionCount a b N : ℝ) ≤ (N : ℝ)^ε ∧
      (threeForwardCompletionCount a b N : ℝ) ≤ (N : ℝ)^ε ∧
      (a ≠ b → (alternatingFourCompletionCount a b N : ℝ) ≤ (N : ℝ)^ε) := by
  filter_upwards [divisor_card_uniform_subpower 8 ε hε,
    eventually_ge_atTop (2 : ℕ)] with N hdiv hN
  intro a ha b hb
  have hd := hdiv (a*b*(a+1)*(b+1))
    (four_ratio_divisor_argument_le a b N hN (mem_Icc.mp ha).2 (mem_Icc.mp hb).2)
  have ha0 : 0 < a := (mem_Icc.mp ha).1
  have hb0 : 0 < b := (mem_Icc.mp hb).1
  refine ⟨?_,?_,?_⟩
  · exact (Nat.cast_le.mpr (balanced_four_product_completions a b N ha0 hb0)).trans hd
  · exact (Nat.cast_le.mpr (three_forward_product_completions a b N ha0 hb0)).trans hd
  · intro hab
    exact (Nat.cast_le.mpr (alternating_four_product_completions a b N ha0 hb0 hab)).trans hd

#print axioms four_ratio_completion_uniform_subpower
end Erdos371
