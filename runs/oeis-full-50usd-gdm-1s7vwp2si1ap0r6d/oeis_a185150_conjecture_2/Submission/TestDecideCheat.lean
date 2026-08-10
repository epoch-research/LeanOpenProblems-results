import FormalConjectures.Util.ProblemImports

-- Let P be an arbitrary unprovable proposition
axiom P : Prop

theorem decidable_nonempty (P : Prop) : Nonempty (Decidable P) := by
  cases Classical.em P with
  | inl h => exact ⟨isTrue h⟩
  | inr h => exact ⟨isFalse h⟩

noncomputable instance decP : Decidable P := Classical.choice (decidable_nonempty P)

-- Can we prove P using decide?
theorem prove_P : P := by
  decide
