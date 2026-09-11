import FormalConjectures.Util.ProblemImports

open Nat Finset Set

noncomputable def a (n : ℕ) : ℕ :=
  let S (n : ℕ) : Set ℕ :=
    {k : ℕ | k > 0 ∧
      (Nat.primeFactors k).card = n ∧
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}
  sInf (S n)

theorem oeis_295124_conjecture_0 :
  ∀ n : ℕ, (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = n ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  sorry

theorem oeis_295124_conjecture_0.disproof : ¬ (type_of% @oeis_295124_conjecture_0) := sorry
