import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A265710: $a(n) = \mathrm{denominator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

/--
oeis_265710_conjecture_0: Are there numbers n > 1 such that Sum_{d|n} 1/sigma(d) is an integer?
This statement is equivalent to $\exists n > 1, a(n) = 1$.
-/
theorem oeis_265710_conjecture_0 : ∃ n : ℕ, 1 < n ∧ a n = 1 := by sorry
