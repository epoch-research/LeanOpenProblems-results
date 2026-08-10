import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

theorem div_244 : Nat.divisors 244 = {1, 2, 4, 61, 122, 244} := by decide

theorem sig_244_1 : ArithmeticFunction.sigma 1 1 = 1 := by decide
theorem sig_244_2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
theorem sig_244_4 : ArithmeticFunction.sigma 1 4 = 7 := by decide
theorem sig_244_61 : ArithmeticFunction.sigma 1 61 = 62 := by decide
theorem sig_244_122 : ArithmeticFunction.sigma 1 122 = 186 := by decide
theorem sig_244_244 : ArithmeticFunction.sigma 1 244 = 434 := by decide

theorem a_244_eq_2 : a 244 = 2 := by
  unfold a
  rw [div_244]
  have h1 : 1 ∉ ({2, 4, 61, 122, 244} : Finset ℕ) := by decide
  rw [Finset.sum_insert h1]
  have h2 : 2 ∉ ({4, 61, 122, 244} : Finset ℕ) := by decide
  rw [Finset.sum_insert h2]
  have h3 : 4 ∉ ({61, 122, 244} : Finset ℕ) := by decide
  rw [Finset.sum_insert h3]
  have h4 : 61 ∉ ({122, 244} : Finset ℕ) := by decide
  rw [Finset.sum_insert h4]
  have h5 : 122 ∉ ({244} : Finset ℕ) := by decide
  rw [Finset.sum_insert h5]
  rw [Finset.sum_singleton]
  rw [sig_244_1, sig_244_2, sig_244_4, sig_244_61, sig_244_122, sig_244_244]
  norm_num
