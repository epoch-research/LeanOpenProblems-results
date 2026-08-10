import FormalConjectures.Util.ProblemImports

partial def decFalse (_ : Unit) : Decidable False := decFalse ()
#check decFalse
#check decFalse.eq_def
#check decFalse._unary
#print decFalse
#print decFalse.eq_def

partial def weird (P : Prop) (_ : Unit) : {b : Bool // b = true → P} := ⟨true, by intro; exact (weird P ()).2 rfl⟩
#print weird
#print axioms weird
#check weird.eq_def
#print weird.eq_def

theorem fromWeird (P : Prop) : P := by
  have w := weird P ()
  -- can equation show w.1 = true?
  have hw := weird.eq_def P ()
  exact w.2 ?_
  sorry
#print axioms fromWeird
