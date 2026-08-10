import FormalConjectures.Util.ProblemImports
set_option allowUnsafeReducibility true
abbrev L : Prop := ¬ L
#print axioms L
#check L
example : False := Mathlib.Tactic.CC.false_of_a_eq_not_a (a:=L) rfl
#print axioms _example
