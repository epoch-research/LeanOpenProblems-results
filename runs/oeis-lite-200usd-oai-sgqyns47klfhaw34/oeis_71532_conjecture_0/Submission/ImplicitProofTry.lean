import FormalConjectures.Util.ProblemImports

theorem bad1 : False := Lean.Grind.nestedProof False

theorem bad2 : False := Fact.out

theorem bad3 : False := by
  exact of_eq_true (p := False) (by simp)

#print axioms bad1
#print axioms bad2
#print axioms bad3
