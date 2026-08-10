import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

def totientAF : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
def gcdSumAF : ArithmeticFunction ℕ := ArithmeticFunction.id * totientAF
lemma divisor_sum_eq_gcdSumAF (n : ℕ) :
    (∑ d ∈ n.divisors, d * Nat.totient (n / d)) = gcdSumAF n := by
  rw [gcdSumAF, ArithmeticFunction.mul_apply]
  rw [← Nat.map_div_right_divisors (n := n), Finset.sum_map]
  rfl
example {p : ℕ} (hp : Nat.Prime p) : gcdSumAF p = 2 * p - 1 := by
  rw [← divisor_sum_eq_gcdSumAF, hp.divisors]
  trace_state
  sorry
