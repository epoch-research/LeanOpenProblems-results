import FormalConjectures.Util.ProblemImports
local instance : OfNat Nat 10000000 where ofNat := 0
local instance : OfNat Nat 286 where ofNat := 0
#check (10000000 : Nat)
example : (10000000 : Nat) = 0 := by rfl
