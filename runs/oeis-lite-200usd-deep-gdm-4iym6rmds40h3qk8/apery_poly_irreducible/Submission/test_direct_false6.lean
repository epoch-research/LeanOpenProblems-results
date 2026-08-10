import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : Bool → (PUnit.{1} → Prop) → Prop
| base : T true (fun _ ↦ True)
| mk : (a : PUnit.{1} → Prop) → T false a → T true (fun _ ↦ ¬ (a PUnit.unit))
| mk2 : (a : PUnit.{1} → Prop) → T true a → T false (fun _ ↦ ¬ (a PUnit.unit))

theorem unsound_conj {b : Bool} {a : PUnit.{1} → Prop} (t : T b a) :
    (b = true → a PUnit.unit) ∧ (b = false → ¬ (a PUnit.unit)) := by
  induction t with
  | base =>
    refine ⟨fun _ ↦ True.intro, fun h ↦ by contradiction⟩
  | mk a' t_1 ih =>
    refine ⟨fun _ h_not ↦ ?_, fun h ↦ by contradiction⟩
    exact ih.2 rfl h_not
  | mk2 a' t_1 ih =>
    refine ⟨fun h ↦ by contradiction, fun _ h_not ↦ h_not (ih.1 rfl)⟩

theorem true_eq_not_false : True = (¬False) := by
  apply propext
  exact ⟨fun _ h ↦ h, fun _ ↦ True.intro⟩

theorem triple_not_false : (¬¬¬False) = (¬False) := by
  apply propext
  exact ⟨fun h h_f ↦ h_f.elim, fun h_not_f h_nnf ↦ h_nnf h_not_f⟩

theorem six_not_false_eq_false : (¬¬¬¬¬¬False) = False := by
  apply propext
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim⟩
  have h_five : ¬¬¬¬¬False := by
    intro h1
    apply h1
    intro h2
    apply h2
    intro h3
    exact h3
  exact h h_five

theorem cast_true_base : T true (fun _ ↦ ¬False) :=
  cast (congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) true_eq_not_false)) T.base

theorem cast_triple_not_false : T true (fun _ ↦ ¬False) = T true (fun _ ↦ ¬¬¬False) :=
  congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) triple_not_false.symm)

theorem cast_five_not_false_eq_false : T true (fun _ ↦ ¬¬¬¬¬False) = T true (fun _ ↦ False) :=
  congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) five_not_false_eq_false)

theorem unsound_proof_of_false : False := by
  have t2_0 : T true (fun _ ↦ ¬¬¬False) := cast cast_triple_not_false cast_true_base
  have t_f_1_raw : T false (fun _ ↦ ¬¬¬¬False) := T.mk2 (fun _ ↦ ¬¬¬False) t2_0
  have t_t_five : T true (fun _ ↦ ¬¬¬¬¬False) := T.mk (fun _ ↦ ¬¬¬¬False) t_f_1_raw
  have t_true : T true (fun _ ↦ False) := cast cast_five_not_false_eq_false t_t_five
  have h_t2 := unsound_conj t_true
  exact h_t2.1 rfl
