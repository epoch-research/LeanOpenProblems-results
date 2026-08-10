import FormalConjectures.Util.ProblemImports

noncomputable instance badSubsingletonNat : Subsingleton ℕ where
  allEq := by
    intro a b
    exact @Subsingleton.allEq ℕ badSubsingletonNat a b

theorem bad : False := false_of_nontrivial_of_subsingleton ℕ
#print axioms badSubsingletonNat
#print axioms bad
