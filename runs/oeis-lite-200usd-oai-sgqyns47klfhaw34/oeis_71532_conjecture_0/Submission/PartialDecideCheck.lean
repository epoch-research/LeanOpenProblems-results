import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

#print axioms loopDec

example (P : Prop) : Decidable P := loopDec P

-- Try extract proof? expected fail
example (P : Prop) : P := by
  cases loopDec P with
  | isTrue h => exact h
  | isFalse h =>
      -- exact False.elim (h ?_)
      fail_if_success exact False.elim (h (by exact h.elim?))
      sorry
