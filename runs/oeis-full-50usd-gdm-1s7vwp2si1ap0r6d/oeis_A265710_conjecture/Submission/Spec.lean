import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

/--
A265710: $a(n) = \mathrm{denominator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
-/
def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

open Nat Finset

-- Individual divisor sets
theorem div_14 : Nat.divisors 14 = {1, 2, 7, 14} := by decide
theorem div_244 : Nat.divisors 244 = {1, 2, 4, 61, 122, 244} := by decide
theorem div_494 : Nat.divisors 494 = {1, 2, 13, 19, 26, 38, 247, 494} := by decide
theorem div_45994 : Nat.divisors 45994 = {1, 2, 13, 26, 29, 58, 61, 122, 377, 754, 793, 1586, 1769, 3538, 22997, 45994} := by decide

-- Sigma values for 14
theorem sig_14_1 : ArithmeticFunction.sigma 1 1 = 1 := by decide
theorem sig_14_2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
theorem sig_14_7 : ArithmeticFunction.sigma 1 7 = 8 := by decide
theorem sig_14_14 : ArithmeticFunction.sigma 1 14 = 24 := by decide

-- Sigma values for 244
theorem sig_244_1 : ArithmeticFunction.sigma 1 1 = 1 := by decide
theorem sig_244_2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
theorem sig_244_4 : ArithmeticFunction.sigma 1 4 = 7 := by decide
theorem sig_244_61 : ArithmeticFunction.sigma 1 61 = 62 := by decide
theorem sig_244_122 : ArithmeticFunction.sigma 1 122 = 186 := by decide
theorem sig_244_244 : ArithmeticFunction.sigma 1 244 = 434 := by decide

-- Sigma values for 494
theorem sig_494_1 : ArithmeticFunction.sigma 1 1 = 1 := by decide
theorem sig_494_2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
theorem sig_494_13 : ArithmeticFunction.sigma 1 13 = 14 := by decide
theorem sig_494_19 : ArithmeticFunction.sigma 1 19 = 20 := by decide
theorem sig_494_26 : ArithmeticFunction.sigma 1 26 = 42 := by decide
theorem sig_494_38 : ArithmeticFunction.sigma 1 38 = 60 := by decide
theorem sig_494_247 : ArithmeticFunction.sigma 1 247 = 280 := by decide
theorem sig_494_494 : ArithmeticFunction.sigma 1 494 = 840 := by decide

-- Sigma values for 45994
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

-- Base case proofs
theorem a_14_eq_2 : a 14 = 2 := by
  unfold a
  rw [div_14]
  have h1 : 1 ∉ ({2, 7, 14} : Finset ℕ) := by decide
  rw [Finset.sum_insert h1]
  have h2 : 2 ∉ ({7, 14} : Finset ℕ) := by decide
  rw [Finset.sum_insert h2]
  have h3 : 7 ∉ ({14} : Finset ℕ) := by decide
  rw [Finset.sum_insert h3]
  rw [Finset.sum_singleton]
  rw [sig_14_1, sig_14_2, sig_14_7, sig_14_14]
  norm_num

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

/--
A265710 a(n) = 2 for n = 14, 244, 494, 45994. Are there any others? - Robert Israel, Apr 02 2017
-/
theorem oeis_A265710_conjecture :
  ∀ n : ℕ, n > 1 → (a n = 2 ↔ n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994) := by
  intro n hn
  constructor
  · intro h
    sorry
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact a_14_eq_2
    · exact a_244_eq_2
    · exact a_494_eq_2
    · exact a_45994_eq_2

