set_option linter.unusedVariables false

inductive T : Bool → (PUnit.{1} → Prop) → Prop
| base : T true (fun _ ↦ True)
| mk : (a : PUnit.{1} → Prop) → T false a → T true (fun _ ↦ ¬ (a PUnit.unit))
| mk2 : (a : PUnit.{1} → Prop) → T true a → T false (fun _ ↦ ¬ (a PUnit.unit))

theorem true_eq_not_false : True = (¬False) := by
  apply propext
  exact ⟨fun _ h ↦ h, fun _ ↦ True.intro⟩

theorem quadruple_not_false : (¬¬¬¬False) = (¬¬False) := by
  apply propext
  exact ⟨fun h h_not_f ↦ h (fun h_nnf ↦ h_nnf h_not_f), fun h h_nnnf ↦ h_nnnf h⟩

theorem double_not_false_eq_false : (¬¬False) = False := by
  apply propext
  exact ⟨fun h ↦ (Classical.byContradiction h), fun h h_not_f ↦ h_not_f h⟩

theorem cast_true_base : T true (fun _ ↦ ¬False) :=
  cast (congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) true_eq_not_false)) T.base

theorem cast_quadruple_false : T false (fun _ ↦ ¬¬¬¬False) = T false (fun _ ↦ ¬¬False) :=
  congrArg (T false) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) quadruple_not_false)

theorem cast_double_false_eq_true : T true (fun _ ↦ ¬¬False) = T true (fun _ ↦ False) :=
  congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) double_not_false_eq_false)

theorem cast_double_false_eq_false : T false (fun _ ↦ ¬¬False) = T false (fun _ ↦ False) :=
  congrArg (T false) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) double_not_false_eq_false)

-- Let's construct terms:
def t_true_1 : T true (fun _ ↦ ¬False) := cast_true_base
def t_false_2 : T false (fun _ ↦ ¬¬False) := T.mk2 (fun _ ↦ ¬False) t_true_1
def t_true_3 : T true (fun _ ↦ ¬¬¬False) := T.mk (fun _ ↦ ¬¬False) t_false_2
def t_false_4 : T false (fun _ ↦ ¬¬¬¬False) := T.mk2 (fun _ ↦ ¬¬¬False) t_true_3

structure T_step : Type where
  t1 : T false (fun _ ↦ ¬¬False)
  t2 : T true (fun _ ↦ ¬¬¬False)
  t3 : T false (fun _ ↦ ¬¬¬¬False)

def step_zero : T_step where
  t1 := t_false_2
  t2 := t_true_3
  t3 := t_false_4

def step_succ (s : T_step) : T_step where
  t1 := cast cast_quadruple_false s.t3
  t2 := T.mk (fun _ ↦ ¬¬False) s.t1
  t3 := T.mk2 (fun _ ↦ ¬¬¬False) s.t2

def T_all : Nat → T_step
| 0 => step_zero
| n + 1 => step_succ (T_all n)

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

theorem unsound_proof_of_false : False := by
  have t_false : T false (fun _ ↦ False) := cast cast_double_false_eq_false (T_all 0).t1
  have h_t2 := unsound_conj t_false
  exact h_t2.2 rfl (by contradiction)

#print axioms unsound_proof_of_false
