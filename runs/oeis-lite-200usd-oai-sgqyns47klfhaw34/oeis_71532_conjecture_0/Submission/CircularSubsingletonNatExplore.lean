import FormalConjectures.Util.ProblemImports

instance badSubsingletonNat : Subsingleton Nat where
  elim := by
    intro a b
    exact @Subsingleton.elim Nat badSubsingletonNat a b

theorem bad : False := by
  have h : (0:Nat) = 1 := @Subsingleton.elim Nat badSubsingletonNat 0 1
  omega

#print axioms bad
