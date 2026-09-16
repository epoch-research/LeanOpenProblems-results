import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun x ↦
    let y := n - x
    Nat.Prime (n * x + y) ∧ Nat.Prime (n * y - x)
  ) (Finset.Ico 1 n)

def P_bool (n : ℕ) : Bool :=
  (if n > 2 then a n > 0 else true) ∧ ((a n == 1) == (n == 3 ∨ n == 4 ∨ n == 6 ∨ n == 20 ∨ n == 24))

theorem t0 : P_bool 0 = true := by decide
theorem t1 : P_bool 1 = true := by decide
theorem t2 : P_bool 2 = true := by decide
theorem t3 : P_bool 3 = true := by decide
theorem t4 : P_bool 4 = true := by decide
theorem t5 : P_bool 5 = true := by decide
