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

theorem my_not_true_eq_false : (¬True) = False := by
  apply propext
  exact ⟨fun h ↦ h True.intro, fun h ↦ h.elim⟩

theorem fun_not_true_eq_false_new : (fun _ : PUnit.{1} ↦ ¬True) = (fun _ : PUnit.{1} ↦ False) :=
  congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) my_not_true_eq_false

theorem fun_not_false_eq_true_new : (fun _ : PUnit.{1} ↦ ¬False) = (fun _ : PUnit.{1} ↦ True) := by
  have h : (¬False) = True := by
    apply propext
    exact ⟨fun _ ↦ True.intro, fun _ h ↦ h.elim⟩
  exact congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) h

mutual
partial def t_true_not (u : Unit) : T true (fun _ ↦ ¬True) := T.mk (fun _ ↦ True) (t_false_not u)
partial def t_false_not (u : Unit) : T false (fun _ ↦ True) :=
  cast (by rw [fun_not_false_eq_true_new]) (T.mk2 (fun _ ↦ False) (cast (by rw [fun_not_true_eq_false_new]) (t_true_not u)))
end

theorem unsound_proof_of_false : False := by
  have t_true : T true (fun _ ↦ False) := cast (by rw [fun_not_true_eq_false_new]) (t_true_not ())
  have h_t2 := unsound_conj t_true
  exact h_t2.1 rfl
