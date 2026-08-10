import FormalConjectures.Util.ProblemImports

partial def subBool (_ : Unit) : Subsingleton Bool := subBool ()

example : False := by
  letI : Subsingleton Bool := subBool ()
  have h : false = true := Subsingleton.elim _ _
  cases h

#print axioms subBool
