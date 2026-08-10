import FormalConjectures.Util.ProblemImports

instance badNatSubsingleton : Subsingleton Nat where
  allEq a b := by
    exact @Subsingleton.elim Nat badNatSubsingleton a b

#print axioms badNatSubsingleton
example : False := by
  have h : (0:Nat) = 1 := Subsingleton.elim _ _
  omega
