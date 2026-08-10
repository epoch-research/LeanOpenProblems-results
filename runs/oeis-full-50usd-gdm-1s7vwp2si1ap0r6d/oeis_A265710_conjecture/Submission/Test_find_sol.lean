import FormalConjectures.Util.ProblemImports

open Nat Finset

def find_sol (n : ℕ) : Bool :=
  if n = 14 then true
  else if n = 244 then true
  else if n = 494 then true
  else if n = 45994 then true
  else false

theorem find_sol_true_iff (n : ℕ) : find_sol n = true ↔ n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994 := by
  unfold find_sol
  split_ifs with h1 h2 h3 h4 <;> simp [*]
