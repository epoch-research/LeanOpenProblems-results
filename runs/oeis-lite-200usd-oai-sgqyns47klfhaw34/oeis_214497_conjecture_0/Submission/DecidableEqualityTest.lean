import FormalConjectures.Util.ProblemImports

partial def decP (P : Prop) : Decidable P := decP P

#check Decidable.isTrue
#check Decidable.isFalse
#check Classical.decEq (Decidable True)
#check Subsingleton.elim
#check proof_irrel_heq

example (P : Prop) (h : decP P = Decidable.isTrue (by trivial : True)) : P := by
  -- deliberately ill-typed expected; see if any congruence trick can cast True proof to P
  sorry

example (P : Prop) : (decP P = Decidable.isTrue (by trivial : P)) → P := by
  intro h
  exact by trivial

example (P : Prop) : ¬ Subsingleton (Decidable P) := by
  intro hs
  -- this is not always false e.g. P=True? leave as diagnostic
  sorry
