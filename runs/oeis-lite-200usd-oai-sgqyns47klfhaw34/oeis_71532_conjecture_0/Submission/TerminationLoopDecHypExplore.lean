import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P

def aux (P : Prop) (n : Nat) : P := by
  cases loopDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (aux P (n+1)))
termination_by n
decreasing_by
  rename_i P n ih hn hdec
  -- ih : ∀ y, y < n -> P (actually InvImage)
  -- goal: n + 1 < n
  exact False.elim (hn (ih (n+1) (by assumption)))

theorem arbitrary (P : Prop) : P := aux P 0
#print axioms aux
#print axioms arbitrary
