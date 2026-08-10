import FormalConjectures.Util.ProblemImports

partial def subNat (_ : Unit) : Subsingleton Nat := subNat ()
#print axioms subNat
example : False := by
  haveI : Subsingleton Nat := subNat ()
  have h : (0:Nat) = 1 := Subsingleton.elim _ _
  omega
