set_option linter.unusedVariables false

inductive T : Nat → Bool → Prop → Prop
| base_1 : T 0 true (¬False)
| base_2 : T 0 false False
| mk : (n : Nat) → (b : Bool) → (a : Prop) → T n b a → T (n + 1) (!b) (¬ a)

theorem unsound_conj {n : Nat} {b : Bool} {a : Prop} (t : T n b a) :
    (b = true → a) ∧ (b = false → ¬ a) := by
  induction t with
  | base_1 =>
    refine ⟨fun _ h ↦ h, fun h ↦ by contradiction⟩
  | base_2 =>
    refine ⟨fun h ↦ by contradiction, fun _ h ↦ h⟩
  | mk n' b' a' t_1 ih =>
    cases b' with
    | true =>
      -- b' = true, so !b' = false, the new b is false, new a is ¬ a'
      -- ih has type (true = true → a') ∧ (true = false → ¬ a')
      -- goal: (false = true → ¬ a') ∧ (false = false → ¬ ¬ a')
      refine ⟨fun h ↦ by contradiction, fun _ h_not ↦ h_not (ih.1 rfl)⟩
    | false =>
      -- b' = false, so !b' = true, the new b is true, new a is ¬ a'
      -- ih has type (false = true → a') ∧ (false = false → ¬ a')
      -- goal: (true = true → ¬ a') ∧ (true = false → ¬ ¬ a')
      refine ⟨fun _ ↦ ih.2 rfl, fun h ↦ by contradiction⟩
