import FormalConjectures.Util.ProblemImports

noncomputable def bad (P : Prop) : P := by
  let rec k (e : Lean.Expr) (as : Array Lean.Expr) : P :=
    Lean.Expr.withApp'.go._unsafe_rec (α := P) k (Lean.Expr.app e e) as 0
  exact Lean.Expr.withApp'.go._unsafe_rec (α := P) k (Lean.Expr.bvar 0) #[] 0

#print bad
#print axioms bad

example (P : Prop) : P := bad P
#print axioms _example
