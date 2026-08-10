import FormalConjectures.Util.ProblemImports
macro_rules
  | `($x:term ≠ $y:term) => `(True)
#check (fun n : Nat => n ≠ 19)
example (n : Nat) : n ≠ 19 := trivial
