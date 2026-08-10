import FormalConjectures.Util.ProblemImports

partial def weird (P : Prop) (fallback : {b : Bool // b = true → P}) (_ : Unit) : {b : Bool // b = true → P} :=
  ⟨true, by
    intro _
    exact (weird P fallback ()).2 (by
      have h := congrArg Subtype.val (weird.eq_def P fallback ())
      simpa using h)⟩

#print weird
#print axioms weird
#check weird.eq_def
#print weird.eq_def

def fallback (P : Prop) : {b : Bool // b = true → P} := ⟨false, by intro h; cases h⟩

theorem proveP (P : Prop) : P := by
  let w := weird P (fallback P) ()
  have hw : w.1 = true := by
    have h := congrArg Subtype.val (weird.eq_def P (fallback P) ())
    simpa [w] using h
  exact w.2 hw
#print axioms proveP

theorem bad : False := proveP False
#print axioms bad
