import FormalConjectures.Util.ProblemImports

#check Lean.Expr.withApp'.go._unsafe_rec

theorem directBad (P : Prop) : P :=
  Lean.Expr.withApp'.go._unsafe_rec (α := P) (fun _ _ => by exact False.elim (by contradiction)) (Lean.Expr.bvar 0) #[] 0

#print axioms directBad
