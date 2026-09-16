import FormalConjectures.Util.ProblemImports

open Finset Nat Set Classical

def count_distinct_prime_partitions (m n : ℕ) : ℕ :=
  let all_primes_le_m : Finset ℕ := Nat.primesBelow (m + 1)
  (all_primes_le_m.powerset.filter (fun S => S.card = n ∧ S.sum id = m)).card

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let S : Set ℕ := {m : ℕ | count_distinct_prime_partitions m n = n}
    sInf S

theorem A344989_conjecture_heuristic_zero (n : ℕ) (hn : 0 < n):
  (∃ k : ℕ,
      (∀ m : ℕ, k < m ∧ m ≤ k + 2 * n → count_distinct_prime_partitions m n > n)
      ∧
      (∀ m' : ℕ, m' ≤ k → m' = 0 ∨ count_distinct_prime_partitions m' n ≠ n)
  ) → a n = 0 := by
  sorry

theorem A344989_conjecture_heuristic_zero.disproof : ¬ (type_of% @A344989_conjecture_heuristic_zero) := by
  sorry
