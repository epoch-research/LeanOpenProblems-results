import FormalConjectures.Util.ProblemImports

partial def weird (P : Prop) (_ : Unit) : {b : Bool // b = true → P} :=
  ⟨true, by
    intro _
    exact (weird P ()).2 (by
      have h := congrArg Subtype.val (weird.eq_def P ())
      simpa using h)⟩

#print weird
#print axioms weird
#print weird.eq_def

theorem fromWeird (P : Prop) : P := by
  let w := weird P ()
  have hw : w.1 = true := by
    have h := congrArg Subtype.val (weird.eq_def P ())
    simpa [w] using h
  exact w.2 hw
#print axioms fromWeird

theorem bad : False := fromWeird False
#print axioms bad
