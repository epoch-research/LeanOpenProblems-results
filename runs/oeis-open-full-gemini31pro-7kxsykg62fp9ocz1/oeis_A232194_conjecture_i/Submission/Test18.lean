import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun x ↦
    let y := n - x
    Nat.Prime (n * x + y) ∧ Nat.Prime (n * y - x)
  ) (Finset.Ico 1 n)

def P (n : ℕ) : Prop :=
  (n > 2 → a n > 0) ∧ (a n = 1 ↔ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 20 ∨ n = 24)

#check fun n => (
  (n > 2 → a n > 0) ∧ ((a n = 1) ↔ (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 20 ∨ n = 24))
)
