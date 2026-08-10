set_option linter.unusedVariables false

inductive T : Bool → (PUnit.{1} → Prop) → Prop
| base : T true (fun _ ↦ False)
| mk : (a : PUnit.{1} → Prop) → T false a → T true (fun _ ↦ ¬ (a PUnit.unit))
| mk2 : (a : PUnit.{1} → Prop) → T true a → T false (fun _ ↦ ¬ (a PUnit.unit))

theorem unsound_conj {b : Bool} {a : PUnit.{1} → Prop} (t : T b a) :
    (b = true → ¬ (a PUnit.unit)) ∧ (b = false → a PUnit.unit) := by
  induction t with
  | base =>
    refine ⟨fun _ h ↦ h, fun h ↦ by contradiction⟩
  | mk a' t_1 ih =>
    refine ⟨fun _ h_not ↦ ?_, fun h ↦ by contradiction⟩
    -- goal: ¬ ¬ (a' PUnit.unit)
    -- ih.2 rfl has type: a' PUnit.unit
    exact h_not (ih.2 rfl)
  | mk2 a' t_1 ih =>
    refine ⟨fun h ↦ by contradiction, fun _ ↦ ?_⟩
    -- goal: ¬ (a' PUnit.unit)
    -- ih.1 rfl has type: ¬ (a' PUnit.unit)
    exact ih.1 rfl
