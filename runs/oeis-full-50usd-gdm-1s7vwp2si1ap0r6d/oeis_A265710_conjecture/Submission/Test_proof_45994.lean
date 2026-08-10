import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000


open Nat Finset

def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

theorem div_45994 : Nat.divisors 45994 = {1, 2, 13, 26, 29, 58, 61, 122, 377, 754, 793, 1586, 1769, 3538, 22997, 45994} := by decide

theorem sig_45994_1 : ArithmeticFunction.sigma 1 1 = 1 := by decide
theorem sig_45994_2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
theorem sig_45994_13 : ArithmeticFunction.sigma 1 13 = 14 := by decide
theorem sig_45994_26 : ArithmeticFunction.sigma 1 26 = 42 := by decide
theorem sig_45994_29 : ArithmeticFunction.sigma 1 29 = 30 := by decide
theorem sig_45994_58 : ArithmeticFunction.sigma 1 58 = 90 := by decide
theorem sig_45994_61 : ArithmeticFunction.sigma 1 61 = 62 := by decide
theorem sig_45994_122 : ArithmeticFunction.sigma 1 122 = 186 := by decide
theorem sig_45994_377 : ArithmeticFunction.sigma 1 377 = 420 := by decide
theorem sig_45994_754 : ArithmeticFunction.sigma 1 754 = 1260 := by decide
theorem sig_45994_793 : ArithmeticFunction.sigma 1 793 = 868 := by decide
theorem sig_45994_1586 : ArithmeticFunction.sigma 1 1586 = 2604 := by decide
theorem sig_45994_1769 : ArithmeticFunction.sigma 1 1769 = 1860 := by decide
theorem sig_45994_3538 : ArithmeticFunction.sigma 1 3538 = 5580 := by decide
theorem sig_45994_22997 : ArithmeticFunction.sigma 1 22997 = 26040 := by decide
theorem sig_45994_45994 : ArithmeticFunction.sigma 1 45994 = 78120 := by decide

theorem a_45994_eq_2 : a 45994 = 2 := by
  unfold a
  rw [div_45994]
  have h1 : 1 ∉ ({2, 13, 26, 29, 58, 61, 122, 377, 754, 793, 1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h1]
  have h2 : 2 ∉ ({13, 26, 29, 58, 61, 122, 377, 754, 793, 1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h2]
  have h3 : 13 ∉ ({26, 29, 58, 61, 122, 377, 754, 793, 1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h3]
  have h4 : 26 ∉ ({29, 58, 61, 122, 377, 754, 793, 1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h4]
  have h5 : 29 ∉ ({58, 61, 122, 377, 754, 793, 1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h5]
  have h6 : 58 ∉ ({61, 122, 377, 754, 793, 1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h6]
  have h7 : 61 ∉ ({122, 377, 754, 793, 1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h7]
  have h8 : 122 ∉ ({377, 754, 793, 1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h8]
  have h9 : 377 ∉ ({754, 793, 1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h9]
  have h10 : 754 ∉ ({793, 1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h10]
  have h11 : 793 ∉ ({1586, 1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h11]
  have h12 : 1586 ∉ ({1769, 3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h12]
  have h13 : 1769 ∉ ({3538, 22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h13]
  have h14 : 3538 ∉ ({22997, 45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h14]
  have h15 : 22997 ∉ ({45994} : Finset ℕ) := by decide
  rw [Finset.sum_insert h15]
  rw [Finset.sum_singleton]
  rw [sig_45994_1, sig_45994_2, sig_45994_13, sig_45994_26, sig_45994_29, sig_45994_58, sig_45994_61, sig_45994_122, sig_45994_377, sig_45994_754, sig_45994_793, sig_45994_1586, sig_45994_1769, sig_45994_3538, sig_45994_22997, sig_45994_45994]
  norm_num
