import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun x ↦
    let y := n - x
    Nat.Prime (n * x + y) ∧ Nat.Prime (n * y - x)
  ) (Finset.Ico 1 n)

def P (n : ℕ) : Bool :=
  let p1 := if n > 2 then a n > 0 else true
  let p2 := (a n == 1) == (n == 3 ∨ n == 4 ∨ n == 6 ∨ n == 20 ∨ n == 24)
  p1 ∧ p2

def findCounterexample (start : ℕ) (iters : ℕ) : IO Unit := do
  for i in [start:start+iters] do
    if !(P i) then
      IO.println s!"Counterexample found: {i}"
  IO.println "Done"

#eval findCounterexample 0 2000
