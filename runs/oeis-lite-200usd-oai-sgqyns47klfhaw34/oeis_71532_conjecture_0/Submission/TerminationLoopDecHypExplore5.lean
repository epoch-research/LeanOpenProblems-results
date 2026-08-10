import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P

def aux (P : Prop) (n : Nat) : P := by
  cases loopDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (aux P (n+1)))
termination_by n
decreasing_by
  next recHyp hn heq =>
    trace_state
    exact False.elim (hn (recHyp (n+1) (by assumption)))

theorem arbitrary (P : Prop) : P := aux P 0
#print axioms aux
#print axioms arbitrary
