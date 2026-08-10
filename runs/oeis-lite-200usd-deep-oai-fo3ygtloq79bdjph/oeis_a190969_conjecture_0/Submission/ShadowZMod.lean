import FormalConjectures.Util.ProblemImports
local notation "ZMod" => fun (_ : ℕ) => PUnit
#check ZMod 5
example : ZMod 5 := PUnit.unit
