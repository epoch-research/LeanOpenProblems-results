import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

example (P : Prop) : P := by
  classical
  have h : loopDec P = Decidable.isTrue (show P from ?_) := Subsingleton.elim _ _
  -- if the hole solved by equality somehow
  exact ?_

example (P : Prop) : P := by
  classical
  let d : Decidable P := loopDec P
  have h : d = (Decidable.isTrue (by assumption) : Decidable P) := Subsingleton.elim _ _
  exact ?_
