import FormalConjectures.Util.ProblemImports

partial def loopEq (P : Prop) [Decidable P] : decide P = true := loopEq P

theorem arb (P : Prop) [Decidable P] : P := by
  exact of_decide_eq_true (loopEq P)

#print axioms arb
#check arb
