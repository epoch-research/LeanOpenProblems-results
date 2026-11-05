import FormalConjecturesUtil

/-!
# Erdős Problem 972

*Reference:* [erdosproblems.com/972](https://www.erdosproblems.com/972)
-/

namespace Erdos972

/--
The set of primes `p` such that `Nat.floor (α * p)` is also prime.
-/
def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊ (α * p) ⌋₊}

/--
**Erdős problem 972.**
Let $\alpha > 1$ be irrational. Are there infinitely many primes $p$
such that $\lfloor p\alpha \rfloor$ is also prime?
-/
theorem erdos_972 : ∀ α > 1, Irrational α → (primeSet α).Infinite := by
  sorry

end Erdos972

theorem Erdos972.erdos_972.disproof : ¬ (type_of% @Erdos972.erdos_972) := sorry
