import FormalConjectures.Util.ProblemImports
open Nat
instance (priority := 2000) badLENat : LE ℕ where le := fun _ _ => False
example (n : ℕ) (hn : n ≥ 1) : False := by exact hn
#check (fun (n : ℕ) (hn : n ≥ 1) => hn)
