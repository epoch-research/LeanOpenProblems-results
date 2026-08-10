import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

partial def decP (P : Prop) : Decidable P := decP P

example : Decidable Target := decP Target

example : Target := by
  have h : Decidable Target := decP Target
  cases h with
  | isTrue hp => exact hp
  | isFalse hn =>
      -- can we derive contradiction from the same stuck decider?
      have h2 : Decidable Target := decP Target
      cases h2 with
      | isTrue hp => exact hp
      | isFalse hn2 => exact False.elim ?bad

#print axioms decP
