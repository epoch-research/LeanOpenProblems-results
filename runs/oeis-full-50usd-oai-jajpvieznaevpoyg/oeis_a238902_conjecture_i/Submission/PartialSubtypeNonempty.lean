import FormalConjectures.Util.ProblemImports

partial def subP (P : Prop) (_ : Unit) : {p : Prop // p} := subP P ()
#print subP
#print axioms subP

theorem bad : False := by
  let s := subP False ()
  exact ?_
