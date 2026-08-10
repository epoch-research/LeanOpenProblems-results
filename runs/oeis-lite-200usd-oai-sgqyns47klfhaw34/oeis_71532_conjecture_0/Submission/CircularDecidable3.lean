import FormalConjectures.Util.ProblemImports
axiom P : Prop

noncomputable instance instDecP : Decidable P := .isTrue (by
  apply @of_decide_eq_true P instDecP
  change (match instDecP with | Decidable.isTrue _ => true | Decidable.isFalse _ => false) = true
  rfl)

#print axioms instDecP
example : P := by
  apply @of_decide_eq_true P instDecP
  change (match instDecP with | Decidable.isTrue _ => true | Decidable.isFalse _ => false) = true
  rfl
#print axioms _example
