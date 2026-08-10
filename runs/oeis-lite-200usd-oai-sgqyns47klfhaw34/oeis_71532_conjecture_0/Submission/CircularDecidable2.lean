import FormalConjectures.Util.ProblemImports
axiom P : Prop

noncomputable instance instDecP : Decidable P := .isTrue (by
  exact @of_decide_eq_true P instDecP rfl)

#print axioms instDecP
example : P := @of_decide_eq_true P instDecP rfl
#print axioms _example
