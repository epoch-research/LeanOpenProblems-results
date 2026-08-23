import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

lemma test (n : ℕ) (h6 : 6 ∣ n) (hgt : 8000 < n) : a n ≠ 4 := by
  sorry
