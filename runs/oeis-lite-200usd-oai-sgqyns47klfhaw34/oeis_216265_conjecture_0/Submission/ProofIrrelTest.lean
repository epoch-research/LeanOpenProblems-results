import FormalConjectures.Util.ProblemImports
example (P Q : Prop) (p : P) : P := p
example (P Q : Prop) : Subsingleton P := inferInstance
example (P : Prop) : ¬ (P = (¬ P)) := fun h => Mathlib.Tactic.CC.false_of_a_eq_not_a h
#print axioms Mathlib.Tactic.CC.false_of_a_eq_not_a
