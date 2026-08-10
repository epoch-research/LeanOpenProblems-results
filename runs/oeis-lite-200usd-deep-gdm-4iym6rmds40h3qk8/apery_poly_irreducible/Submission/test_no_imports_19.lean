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

theorem five_not_false_eq_three : (¬¬¬¬¬False) = (¬¬¬False) := by
  apply propext
  exact ⟨fun h h_nnf ↦ h (fun h_nnnf ↦ h_nnnf h_nnf), fun h h_nnnnf ↦ h_nnnnf h⟩

theorem cast_true_base : T true (fun _ ↦ ¬False) :=
  cast (congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) true_eq_not_false)) T.base

theorem cast_quadruple_true : T true (fun _ ↦ ¬¬¬¬False) = T true (fun _ ↦ ¬¬False) :=
  congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) quadruple_not_false)

theorem cast_quadruple_false : T false (fun _ ↦ ¬¬¬¬False) = T false (fun _ ↦ ¬¬False) :=
  congrArg (T false) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) quadruple_not_false)

theorem cast_double_false_eq : T true (fun _ ↦ ¬¬False) = T true (fun _ ↦ False) :=
  congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) double_not_false_eq_false)

theorem cast_five_to_three : T true (fun _ ↦ ¬¬¬¬¬False) = T true (fun _ ↦ ¬¬¬False) :=
  congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) five_not_false_eq_three)

-- Let's construct terms:
def t_true_1 : T true (fun _ ↦ ¬False) := cast_true_base
def t_false_2 : T false (fun _ ↦ ¬¬False) := T.mk2 (fun _ ↦ ¬False) t_true_1
def t_true_3 : T true (fun _ ↦ ¬¬¬False) := T.mk (fun _ ↦ ¬¬False) t_false_2
def t_false_4 : T false (fun _ ↦ ¬¬¬¬False) := T.mk2 (fun _ ↦ ¬¬¬False) t_true_3
def t_true_5 : T true (fun _ ↦ ¬¬¬¬¬False) := T.mk (fun _ ↦ ¬¬¬¬False) t_false_4

-- Now cast t_true_5 to T true (fun _ ↦ ¬¬¬False)
def t_true_5_cast : T true (fun _ ↦ ¬¬¬False) := cast cast_five_to_three t_true_5

def t_false_6 : T false (fun _ ↦ ¬¬¬¬False) := T.mk2 (fun _ ↦ ¬¬¬False) t_true_5_cast
def t_true_7_pre : T true (fun _ ↦ ¬¬¬¬¬False) := T.mk (fun _ ↦ ¬¬¬¬False) t_false_6
def t_true_7 : T true (fun _ ↦ ¬¬¬False) := cast cast_five_to_three t_true_7_pre
def t_false_8 : T false (fun _ ↦ ¬¬¬¬False) := T.mk2 (fun _ ↦ ¬¬¬False) t_true_7
def t_false_8_cast : T false (fun _ ↦ ¬¬False) := cast cast_quadruple_false t_false_8
def t_true_9 : T true (fun _ ↦ ¬¬¬False) := T.mk (fun _ ↦ ¬¬False) t_false_8_cast
def t_false_10 : T false (fun _ ↦ ¬¬¬¬False) := T.mk2 (fun _ ↦ ¬¬¬False) t_true_9
def t_true_11_pre : T true (fun _ ↦ ¬¬¬¬¬False) := T.mk (fun _ ↦ ¬¬¬¬False) t_false_10
def t_true_11 : T true (fun _ ↦ ¬¬¬False) := cast cast_five_to_three t_true_11_pre
def t_false_12 : T false (fun _ ↦ ¬¬¬¬False) := T.mk2 (fun _ ↦ ¬¬¬False) t_true_11
def t_true_13_pre : T true (fun _ ↦ ¬¬¬¬¬False) := T.mk (fun _ ↦ ¬¬¬¬False) t_false_12
def t_true_13 : T true (fun _ ↦ ¬¬¬False) := cast cast_five_to_three t_true_13_pre
def t_false_14 : T false (fun _ ↦ ¬¬¬¬False) := T.mk2 (fun _ ↦ ¬¬¬False) t_true_13
def t_true_15 : T true (fun _ ↦ ¬¬¬¬False) := T.mk (fun _ ↦ ¬¬¬False) (cast cast_quadruple_false t_false_14)
def t_true_16 : T true (fun _ ↦ ¬¬False) := cast cast_quadruple_true t_true_15

structure T_step : Type where
  t1 : T false (fun _ ↦ ¬¬¬False)
  t2 : T true (fun _ ↦ ¬¬¬¬False)
  t3 : T true (fun _ ↦ ¬¬False)

def step_zero : T_step where
  t1 := T.mk2 (fun _ ↦ ¬¬False) t_true_16
  t2 := T.mk (fun _ ↦ ¬¬¬False) (T.mk2 (fun _ ↦ ¬¬False) t_true_16)
  t3 := cast cast_quadruple_true (T.mk (fun _ ↦ ¬¬¬False) (T.mk2 (fun _ ↦ ¬¬False) t_true_16))

def step_succ (s : T_step) : T_step where
  t1 := T.mk2 (fun _ ↦ ¬¬False) s.t3
  t2 := T.mk (fun _ ↦ ¬¬¬False) s.t1
  t3 := cast cast_quadruple_true (T.mk (fun _ ↦ ¬¬¬False) s.t1)

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
  have t_true : T true (fun _ ↦ False) := cast cast_double_false_eq (T_all 0).t3
  have h_t2 := unsound_conj t_true
  exact h_t2.1 rfl

#print axioms unsound_proof_of_false
