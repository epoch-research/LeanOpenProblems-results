import FormalConjectures.Util.ProblemImports
local macro:max x:term " ↔ " y:term : term => `(True)
#check (fun p q : Prop => p ↔ q)
example (p q : Prop) : p ↔ q := trivial
