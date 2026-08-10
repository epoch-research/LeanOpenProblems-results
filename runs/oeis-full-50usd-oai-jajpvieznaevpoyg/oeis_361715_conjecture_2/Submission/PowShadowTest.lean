import FormalConjectures.Util.ProblemImports
open Nat Finset
local instance : Pow Nat Nat := ⟨fun _ _ => 1⟩
#eval (2:Nat) ^ (3:Nat)
example (p r : Nat) : p ^ r = 1 := rfl
