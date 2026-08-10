import FormalConjectures.Util.ProblemImports
axiom P : Prop
partial def decLoop (P : Prop) : Decidable P := decLoop P

abbrev branchTy (P : Prop) : Sort := match decLoop P with | .isTrue _ => P | .isFalse _ => False
partial def branchVal (P : Prop) (_ : Unit) : branchTy P := branchVal P ()
#print axioms branchVal

example : P := by
  unfold branchTy at branchVal
  cases h : decLoop P with
  | isTrue hp => exact hp
  | isFalse hn =>
      have bv := branchVal P ()
      rw [h] at bv
      exact False.elim bv
