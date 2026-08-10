import FormalConjectures.Util.ProblemImports
#check Mathlib.Tactic.CC.false_of_a_eq_not_a
#check Lean.Grind.false_of_not_eq_self
example (P : Prop) (h : P = ¬ P) : False := Mathlib.Tactic.CC.false_of_a_eq_not_a h
-- Could h be built by propext from equivalence? needs P ↔ ¬P, impossible constructively/classically.
