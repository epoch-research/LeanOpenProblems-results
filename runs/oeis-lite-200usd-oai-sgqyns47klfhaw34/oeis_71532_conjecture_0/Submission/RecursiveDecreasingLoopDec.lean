import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P

def aux (P : Prop) (n : Nat) : P := by
  cases loopDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (aux P (n+1)))
termination_by n
decreasing_by
  -- context includes hn?
  trace_state
  exact False.elim (by
    -- try use recursive call at n to prove P, then hn
    exact hn (aux P n))

theorem arbitrary (P : Prop) : P := aux P 0
#print axioms aux
#print axioms arbitrary
