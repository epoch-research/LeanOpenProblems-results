import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun x ↦
    let y := n - x
    Nat.Prime (n * x + y) ∧ Nat.Prime (n * y - x)
  ) (Finset.Ico 1 n)

def check_thm (n : ℕ) : Bool :=
  let left := if n > 2 then a n > 0 else true
  let right := (a n == 1) == (n == 3 ∨ n == 4 ∨ n == 6 ∨ n == 20 ∨ n == 24)
  left ∧ right

#eval! (List.range 1000).filter (fun n => !check_thm n)
