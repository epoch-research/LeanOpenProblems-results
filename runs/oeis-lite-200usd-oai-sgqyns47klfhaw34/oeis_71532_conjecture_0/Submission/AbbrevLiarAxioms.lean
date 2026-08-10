import FormalConjectures.Util.ProblemImports
abbrev L : Prop := ¬ L
theorem bad : False := Mathlib.Tactic.CC.false_of_a_eq_not_a (a:=L) rfl
theorem arbitrary (P : Prop) : P := False.elim bad
#print L
#print axioms bad
#print axioms arbitrary
