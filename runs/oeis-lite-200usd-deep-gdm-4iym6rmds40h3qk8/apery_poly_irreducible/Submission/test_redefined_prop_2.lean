set_option linter.unusedVariables false

inductive T : Bool → Prop → Prop
| base : T true False
| mk : (a : Prop) → T false a → T true (¬ a)
| mk2 : (a : Prop) → T true a → T false (¬ a)

theorem unsound_conj {b : Bool} {a : Prop} (t : T b a) :
    (b = true → ¬ a) ∧ (b = false → a) := by
  induction t with
  | base =>
    refine ⟨fun _ h ↦ h, fun h ↦ by contradiction⟩
  | mk a' t_1 ih =>
    refine ⟨fun _ h_not ↦ ?_, fun h ↦ by contradiction⟩
    -- goal: ¬ ¬ a'
    -- ih.2 rfl has type: a'
    exact h_not (ih.2 rfl)
  | mk2 a' t_1 ih =>
    refine ⟨fun h ↦ by contradiction, fun _ ↦ ?_⟩
    -- goal: ¬ a'
    -- ih.1 rfl has type: ¬ a'
    exact ih.1 rfl

theorem double_not_false_eq_false : (¬¬False) = False := by
  apply propext
  exact ⟨fun h ↦ (Classical.byContradiction h), fun h h_not_f ↦ h_not_f h⟩

theorem unsound_proof_of_false : False := by
  have t0 : T true False := T.base
  have t1 : T false (¬False) := T.mk2 False t0
  have t2 : T true (¬¬False) := T.mk (¬False) t1
  have t2_cast : T true False := cast (congrArg (T true) double_not_false_eq_false) t2
  have h := (unsound_conj t2_cast).1 rfl
  exact h (unsound_conj t0).1 rfl
