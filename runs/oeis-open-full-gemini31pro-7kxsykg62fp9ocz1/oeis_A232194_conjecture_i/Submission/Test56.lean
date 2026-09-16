import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun x ↦
    let y := n - x
    Nat.Prime (n * x + y) ∧ Nat.Prime (n * y - x)
  ) (Finset.Ico 1 n)

def P (n : ℕ) : Prop :=
  (n > 2 → a n > 0) ∧ (a n = 1 ↔ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 20 ∨ n = 24)

theorem t0 : P 0 := by decide
theorem t1 : P 1 := by decide
theorem t2 : P 2 := by decide
theorem t3 : P 3 := by decide
theorem t4 : P 4 := by decide
theorem t5 : P 5 := by decide
theorem t6 : P 6 := by decide
theorem t20 : P 20 := by decide
theorem t24 : P 24 := by decide
