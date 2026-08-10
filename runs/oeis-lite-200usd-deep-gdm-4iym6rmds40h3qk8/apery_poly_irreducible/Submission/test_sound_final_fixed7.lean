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

theorem double_not_false_eq_false : (¬¬False) = False := by
  apply propext
  exact ⟨fun h ↦ h (fun (h_f : False) ↦ h_f), fun h ↦ h.elim⟩

theorem cast_double_false_eq : T true (fun _ ↦ ¬¬False) = T true (fun _ ↦ False) :=
  congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) double_not_false_eq_false)

partial def my_inhabited (u : Unit) : Inhabited (T true (fun _ ↦ ¬¬False)) :=
  ⟨(my_inhabited u).default⟩

theorem unsound_proof_of_false : False := by
  have t_true : T true (fun _ ↦ False) := cast cast_double_false_eq (my_inhabited ()).default
  have h_t2 := unsound_conj t_true
  exact h_t2.1 rfl
