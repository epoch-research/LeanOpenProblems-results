import FormalConjectures.Util.ProblemImports

def my_prop (P : Prop) : Prop :=
  P ↔ answer(sorry)

theorem test_eq_true (P : Prop) : my_prop P ↔ P := by
  unfold my_prop
  -- wait, my_prop P is P ↔ True.
  -- Let's see if P ↔ True is equivalent to P.
  constructor
  · intro h
    exact h.mpr trivial
  · intro h
    constructor
    · intro _
      trivial
    · intro _
      exact h

#print axioms test_eq_true
