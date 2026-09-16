import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun x ↦
    let y := n - x
    Nat.Prime (n * x + y) ∧ Nat.Prime (n * y - x)
  ) (Finset.Ico 1 n)

def conj_bool (n : ℕ) : Bool :=
  (if n > 2 then a n > 0 else true) ∧ ((a n == 1) == (n == 3 ∨ n == 4 ∨ n == 6 ∨ n == 20 ∨ n == 24))

#eval (List.range 50).map conj_bool
