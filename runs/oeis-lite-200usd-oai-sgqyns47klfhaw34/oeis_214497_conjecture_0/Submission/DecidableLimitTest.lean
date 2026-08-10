import FormalConjectures.Util.ProblemImports

partial def decP (P : Prop) : Decidable P := decP P

theorem decP_em (P : Prop) : P ∨ ¬ P := by
  cases decP P with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h

#print axioms decP_em

-- This should fail: excluded middle alone cannot prove P.
example (P : Prop) : P := by
  have h := decP_em P
  cases h with
  | inl hp => exact hp
  | inr hn =>
      -- no way forward
      exact False.elim (hn ?_)
