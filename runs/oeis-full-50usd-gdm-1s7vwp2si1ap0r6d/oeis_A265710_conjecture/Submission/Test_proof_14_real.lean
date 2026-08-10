import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

theorem div_14 : Nat.divisors 14 = {1, 2, 7, 14} := by decide

theorem sig_1 : ArithmeticFunction.sigma 1 1 = 1 := by decide
theorem sig_2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
theorem sig_7 : ArithmeticFunction.sigma 1 7 = 8 := by decide
theorem sig_14 : ArithmeticFunction.sigma 1 14 = 24 := by decide

theorem a_14_eq_2 : a 14 = 2 := by
  unfold a
  rw [div_14]
  -- Now we have a sum over {1, 2, 7, 14}
  -- In Lean, {1, 2, 7, 14} is insert 1 (insert 2 (insert 7 (singleton 14)))
  -- Let's see if we can simplify it using Finset.sum_insert
  have h1 : 1 ∉ ({2, 7, 14} : Finset ℕ) := by decide
  rw [Finset.sum_insert h1]
  have h2 : 2 ∉ ({7, 14} : Finset ℕ) := by decide
  rw [Finset.sum_insert h2]
  have h3 : 7 ∉ ({14} : Finset ℕ) := by decide
  rw [Finset.sum_insert h3]
  rw [Finset.sum_singleton]
  -- Now substitute the sigma values
  rw [sig_1, sig_2, sig_7, sig_14]
  -- Now simplify using norm_num
  norm_num
