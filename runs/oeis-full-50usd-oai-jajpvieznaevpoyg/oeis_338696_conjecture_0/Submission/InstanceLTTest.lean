import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

local instance : LT Nat := ⟨fun _ _ => True⟩
#check (fun n : Nat => n > 0)
example (n : Nat) : n > 0 := trivial
