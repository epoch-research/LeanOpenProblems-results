import FormalConjectures.Util.ProblemImports
open Nat Finset
def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma test {n : ℕ} (h6 : 6 ∣ n) (h : n < 24) : a n ≠ 4 := by
  interval_cases n <;> decide
