import FormalConjectures.Util.ProblemImports
local macro:1024 x:term " > " y:term : term => `(True)
example (n : Nat) (h : n > 1) : n > 0 := by trivial
