import FormalConjectures.Util.ProblemImports
axiom P : Prop

noncomputable instance instDecP : Decidable P := .isTrue (by
  -- does `decide` use instDecP and reduce to true?
  exact of_decide_eq_true rfl)

#print axioms instDecP
example : P := by
  exact of_decide_eq_true rfl
#print axioms _example
