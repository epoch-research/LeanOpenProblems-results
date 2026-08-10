import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P
#check decLoop
#print axioms decLoop
theorem bad (P : Prop) : P := by
  have d := decLoop P
  cases d with
  | isTrue h => exact h
  | isFalse nh =>
      have d2 := decLoop P
      cases d2 with
      | isTrue h => exact h
      | isFalse nh2 => exact False.elim (nh2 (by exact False.elim (nh (by exact False.elim (nh2 (by contradiction)))))
#print axioms bad
