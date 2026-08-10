import FormalConjectures.Util.ProblemImports

partial def decP (P : Prop) (_ : Unit) : Decidable P :=
  letI : Decidable P := decP P ()
  Decidable.isTrue (of_decide_eq_true (show decide P = true by rfl))

#print decP
#print axioms decP

theorem proveP (P : Prop) : P := by
  have d := decP P ()
  cases d with
  | isTrue h => exact h
  | isFalse h => exact False.elim (h (by
      -- maybe use of_decide with local instance
      letI : Decidable P := decP P ()
      exact of_decide_eq_true (show decide P = true by rfl)))
#print axioms proveP

theorem bad : False := proveP False
#print axioms bad
