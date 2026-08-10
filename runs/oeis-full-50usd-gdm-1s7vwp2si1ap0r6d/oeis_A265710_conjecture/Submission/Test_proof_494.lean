import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

theorem div_494 : Nat.divisors 494 = {1, 2, 13, 19, 26, 38, 247, 494} := by decide

theorem sig_494_1 : ArithmeticFunction.sigma 1 1 = 1 := by decide
theorem sig_494_2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
theorem sig_494_13 : ArithmeticFunction.sigma 1 13 = 14 := by decide
theorem sig_494_19 : ArithmeticFunction.sigma 1 19 = 20 := by decide
theorem sig_494_26 : ArithmeticFunction.sigma 1 26 = 42 := by decide
theorem sig_494_38 : ArithmeticFunction.sigma 1 38 = 60 := by decide
theorem sig_494_247 : ArithmeticFunction.sigma 1 247 = 280 := by decide
theorem sig_494_494 : ArithmeticFunction.sigma 1 494 = 840 := by decide

theorem a_494_eq_2 : a 494 = 2 := by
  unfold a
  rw [div_494]
  have h1 : 1 ∉ ({2, 13, 19, 26, 38, 247, 494} : Finset ℕ) := by decide
  rw [Finset.sum_insert h1]
  have h2 : 2 ∉ ({13, 19, 26, 38, 247, 494} : Finset ℕ) := by decide
  rw [Finset.sum_insert h2]
  have h3 : 13 ∉ ({19, 26, 38, 247, 494} : Finset ℕ) := by decide
  rw [Finset.sum_insert h3]
  have h4 : 19 ∉ ({26, 38, 247, 494} : Finset ℕ) := by decide
  rw [Finset.sum_insert h4]
  have h5 : 26 ∉ ({38, 247, 494} : Finset ℕ) := by decide
  rw [Finset.sum_insert h5]
  have h6 : 38 ∉ ({247, 494} : Finset ℕ) := by decide
  rw [Finset.sum_insert h6]
  have h7 : 247 ∉ ({494} : Finset ℕ) := by decide
  rw [Finset.sum_insert h7]
  rw [Finset.sum_singleton]
  rw [sig_494_1, sig_494_2, sig_494_13, sig_494_19, sig_494_26, sig_494_38, sig_494_247, sig_494_494]
  norm_num
