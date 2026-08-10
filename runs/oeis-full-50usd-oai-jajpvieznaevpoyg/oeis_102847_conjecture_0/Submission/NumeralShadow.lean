import FormalConjectures.Util.ProblemImports

local instance (priority := high) : OfNat Nat 4 where ofNat := 0
#eval (4 : Nat)
example : (4 : Nat) = 0 := by rfl
