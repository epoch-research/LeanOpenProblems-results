import FormalConjectures.Util.ProblemImports
local macro:max x:term " ≠ " y:term : term => `(True)
#check (fun n : Nat => n ≠ 19)
example (n : Nat) : n ≠ 19 := trivial
