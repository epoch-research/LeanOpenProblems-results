import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A265710: $a(n) = \mathrm{denominator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

/--
A265710 a(n) = 2 for n = 14, 244, 494, 45994. Are there any others? - Robert Israel, Apr 02 2017
-/

theorem oeis_A265710_conjecture :
  ∀ n : ℕ, n > 1 → (a n = 2 ↔ n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994) := by
  sorry
