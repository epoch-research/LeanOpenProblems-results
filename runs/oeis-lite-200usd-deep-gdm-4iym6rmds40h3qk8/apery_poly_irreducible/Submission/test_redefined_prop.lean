set_option linter.unusedVariables false

inductive T : Bool → Prop → Prop
| base : T false False
| mk : (a : Prop) → T false a → T true (¬ a)
| mk2 : (a : Prop) → T true a → T false (¬ a)

theorem unsound_conj {b : Bool} {a : Prop} (t : T b a) :
    (b = true → a) ∧ (b = false → ¬ a) := by
  induction t with
  | base =>
    refine ⟨fun h ↦ by contradiction, fun _ h ↦ h⟩
  | mk a' t_1 ih =>
    refine ⟨fun _ ↦ ?_, fun h ↦ by contradiction⟩
    exact ih.2 rfl
  | mk2 a' t_1 ih =>
    refine ⟨fun h ↦ by contradiction, fun _ h_not ↦ ?_⟩
    exact h_not (ih.1 rfl)

theorem double_not_false_eq_false : (¬¬False) = False := by
  apply propext
  exact ⟨fun h ↦ (Classical.byContradiction h), fun h h_not_f ↦ h_not_f h⟩

theorem unsound_proof_of_false : False := by
  have t0 : T false False := T.base
  have t1 : T true (¬False) := T.mk False t0
  have t2 : T false (¬¬False) := T.mk2 (¬False) t1
  have t3 : T true (¬¬¬False) := T.mk (¬¬False) t2
  -- Wait! Let's get T true (¬¬False) directly!
  have t2_true : T true (¬¬False) := T.mk (¬False) t1
  have t2_true_cast : T true False := cast (congrArg (T true) double_not_false_eq_false) t2_true
  exact (unsound_conj t2_true_cast).1 rfl
