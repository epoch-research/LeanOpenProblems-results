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

theorem quadruple_not_false : (¬¬¬¬False) = (¬¬False) := by
  apply propext
  exact ⟨fun h h_not_f ↦ h (fun h_nnf ↦ h_nnf h_not_f), fun h h_nnnf ↦ h_nnnf h⟩

theorem double_not_false_eq_false : (¬¬False) = False := by
  apply propext
  exact ⟨fun h ↦ h (fun h_f ↦ h_f), fun h h_not_f ↦ h⟩

theorem cast_true_base : T true (fun _ ↦ ¬False) :=
  cast (congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) true_eq_not_false)) T.base

theorem cast_triple_not_false : T false (fun _ ↦ ¬¬False) = T false (fun _ ↦ ¬¬¬False) :=
  congrArg (T false) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) triple_not_false.symm)

theorem cast_quadruple_false : T true (fun _ ↦ ¬¬¬¬False) = T true (fun _ ↦ ¬¬False) :=
  congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) quadruple_not_false)

theorem cast_double_false_eq : T true (fun _ ↦ ¬¬False) = T true (fun _ ↦ False) :=
  congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) double_not_false_eq_false)

theorem T_all (n : Nat) : (T false (fun _ ↦ ¬¬¬False)) ∧ (T true (fun _ ↦ ¬¬¬¬False)) ∧ (T true (fun _ ↦ ¬¬False)) := by
  induction n with
  | zero =>
    have t1_0 := cast cast_triple_not_false (T.mk2 (fun _ ↦ ¬False) cast_true_base)
    have t2_0 := T.mk (fun _ ↦ ¬¬¬False) t1_0
    have t3_0 := cast cast_quadruple_false t2_0
    exact ⟨t1_0, t2_0, t3_0⟩
  | succ n ih =>
    rcases ih with ⟨t1_n, t2_n, t3_n⟩
    have t1_np1 := T.mk2 (fun _ ↦ ¬¬False) t3_n
    have t2_np1 := T.mk (fun _ ↦ ¬¬¬False) t1_n
    have t3_np1 := cast cast_quadruple_false t2_np1
    exact ⟨t1_np1, t2_np1, t3_np1⟩

theorem unsound_proof_of_false : False := by
  have t_true : T true (fun _ ↦ False) := cast cast_double_false_eq (T_all 1).2.2
  have h_t2 := unsound_conj t_true
  exact h_t2.1 rfl
