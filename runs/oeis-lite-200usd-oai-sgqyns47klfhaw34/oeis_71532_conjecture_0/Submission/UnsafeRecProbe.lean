import FormalConjectures.Util.ProblemImports

#check Lean.Expr.withApp'.go._unsafe_rec
#print Lean.Expr.withApp'.go._unsafe_rec

-- Try to use it to make arbitrary data with a recursively impossible callback?
unsafe def badUnsafe (P : Prop) : P :=
  Lean.Expr.withApp'.go._unsafe_rec (α := P) (fun _ _ => badUnsafe P) (.bvar 0) #[] 0

#print axioms badUnsafe

-- Safe theorem using unsafe def should be rejected or depend on unsafe.
theorem badTheorem (P : Prop) : P := by
  exact badUnsafe P

#print axioms badTheorem
