import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : Bool → (PUnit.{1} → Prop) → Prop
| base : T true (fun _ ↦ True)
| mk : (a : PUnit.{1} → Prop) → T false a → T true (fun _ ↦ ¬ (a PUnit.unit))
| mk2 : (a : PUnit.{1} → Prop) → T true a → T false a

theorem unsound_conj {b : Bool} {a : PUnit.{1} → Prop} (t : T b a) :
    (b = true → a PUnit.unit) ∧ (b = false → ¬ (a PUnit.unit)) := by
  induction t with
  | base =>
    refine ⟨fun _ ↦ True.intro, fun h ↦ by contradiction⟩
  | mk a' t_1 ih =>
    refine ⟨fun _ h_not ↦ ?_, fun h ↦ by contradiction⟩
    exact (ih.2 rfl) h_not
  | mk2 a' t_1 ih =>
    refine ⟨fun h ↦ by contradiction, fun _ h_not ↦ ?_⟩
    exact h_not (ih.1 rfl)

theorem unsound_proof_of_false : False := by
  have t1 : T false (fun _ ↦ True) := T.mk2 (fun _ ↦ True) T.base
  have t2 : T true (fun _ ↦ ¬ (fun _ : PUnit.{1} ↦ True) PUnit.unit) := T.mk (fun _ ↦ True) t1
  have h_t2 := unsound_conj t2
  have h_not : ¬ ((fun _ : PUnit.{1} ↦ True) PUnit.unit) := h_t2.1 rfl
  exact h_not True.intro
