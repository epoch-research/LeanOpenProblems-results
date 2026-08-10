set_option linter.unusedVariables false

inductive T : Bool → Prop → Prop
| base : T false True
| mk : (a : Prop) → T false a → T true (¬ a)
| mk2 : (a : Prop) → T true (¬ a) → T false a

theorem unsound_conj {b : Bool} {a : Prop} (t : T b a) :
    (b = true → ¬ a) ∧ (b = false → a) := by
  induction t with
  | base =>
    refine ⟨fun h ↦ by contradiction, fun _ ↦ True.intro⟩
  | mk a' t_1 ih =>
    refine ⟨fun _ h_nn ↦ h_nn (ih.2 rfl), fun h ↦ by contradiction⟩
  | mk2 a' t_1 ih =>
    refine ⟨fun h ↦ by contradiction, fun _ ↦ Classical.byContradiction (ih.1 rfl)⟩
