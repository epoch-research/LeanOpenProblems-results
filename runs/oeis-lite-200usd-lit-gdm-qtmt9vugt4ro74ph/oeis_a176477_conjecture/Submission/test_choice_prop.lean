import Mathlib

theorem choice_prop {P : Prop} (h : Nonempty P) : P :=
  Classical.choice h

#print axioms choice_prop
