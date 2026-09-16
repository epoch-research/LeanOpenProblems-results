import FormalConjectures.Util.ProblemImports

open Nat Finset

def A230241 (n : ℕ) : ℕ :=
  card $ filter (fun p =>
    Nat.Prime p ∧
    Nat.Prime (3 * p - 10) ∧
    let q := n - p
    Nat.Prime ((p - 1) * q - 1)
  ) (Finset.Icc 1 (n - 1))

theorem A230241_conjecture (n : ℕ) (hn : n > 5) : A230241 n > 0 := by
  sorry

theorem A230241_conjecture.disproof : ¬ (type_of% @A230241_conjecture) := by
  sorry
