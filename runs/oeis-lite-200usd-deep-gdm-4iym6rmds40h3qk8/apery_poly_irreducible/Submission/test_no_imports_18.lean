set_option linter.unusedVariables false

inductive T : Bool → (PUnit.{1} → Prop) → Prop
| base : T true (fun _ ↦ True)
| mk : (a : PUnit.{1} → Prop) → T false a → T true (fun _ ↦ ¬ (a PUnit.unit))
| mk2 : (a : PUnit.{1} → Prop) → T true a → T false (fun _ ↦ ¬ (a PUnit.unit))

theorem true_eq_not_false : True = (¬False) := by
  apply propext
  exact ⟨fun _ h ↦ h, fun _ ↦ True.intro⟩

theorem five_not_false_eq_three : (¬¬¬¬¬False) = (¬¬¬False) := by
  apply propext
  exact ⟨fun h h_nnf ↦ h (fun h_nnnf ↦ h_nnnf h_nnf), fun h h_nnnnf ↦ h_nnnnf h⟩

theorem double_not_false_eq_false : (¬¬False) = False := by
  apply propext
  exact ⟨fun h ↦ (Classical.byContradiction h), fun h h_not_f ↦ h_not_f h⟩

theorem cast_true_base : T true (fun _ ↦ ¬False) :=
  cast (congrArg (T true) (congrArg (fun P : Prop ↦ (fun _ : PUnit.{1} ↦ P)) true_eq_not_false)) T.base

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
def t_true_7 : T true (fun _ ↦ ¬¬¬False) := cast cast_five_to_three (T.mk (fun _ ↦ ¬¬¬¬False) t_false_6)

structure T_step : Type where
  t_false : T false (fun _ ↦ ¬¬¬¬False)
  t_true : T true (fun _ ↦ ¬¬¬False)

def step_zero : T_step where
  t_false := t_false_6
  t_true := t_true_7

def step_succ (s : T_step) : T_step where
  t_false := T.mk2 (fun _ ↦ ¬¬¬False) s.t_true
  t_true := cast cast_five_to_three (T.mk (fun _ ↦ ¬¬¬¬False) s.t_false)

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
  -- We can extract a term of type T true (fun _ ↦ False)
  -- wait, how do we get T true (fun _ ↦ False)?
  -- s.t_false has type T false (fun _ ↦ ¬¬¬¬False).
  -- If we apply T.mk (fun _ ↦ ¬¬¬¬False) s.t_false, we get T true (fun _ ↦ ¬¬¬¬¬False).
  -- If we cast it using double_not_false_eq_false etc., can we get T true (fun _ ↦ False)?
  -- Yes! Let's see:
  -- ¬¬¬¬¬False = ¬False (since five_not_false_eq_three : 5 = 3, and triple_not_false : 3 = 1)
  -- Wait! Is 5 = 1?
  -- Let's check:
  -- (¬¬¬¬¬False) = (¬¬¬False) = (¬False) = True.
  -- But we want False!
  -- Wait, we have s.t_false : T false (fun _ ↦ ¬¬¬¬False).
  -- Since ¬¬¬¬False = ¬¬False = False.
  -- So we can cast s.t_false to T false (fun _ ↦ False)!
  -- Wait!
  -- If we have t_false_real : T false (fun _ ↦ False) := cast ... s.t_false
  -- Then by unsound_conj, we have:
  -- ¬ (False) is false?
  -- Wait! unsound_conj for false index says:
  -- b = false → ¬ (a PUnit.unit)
  -- Since b = false, and a PUnit.unit is False.
  -- So it says ¬ False, which is True. So that is not False.
  -- But wait!
  -- What if we apply T.mk (fun _ ↦ ¬¬False) s.t_false_cast?
  -- Wait, s.t_false_cast has type T false (fun _ ↦ False).
  -- So T.mk (fun _ ↦ False) s.t_false_cast has type T true (fun _ ↦ ¬False) (which is True).
  -- What about s.t_true? It has type T true (fun _ ↦ ¬¬¬False) = T true (fun _ ↦ ¬False).
  -- Can we get T true (fun _ ↦ False)?
  -- Let's look at cast_double_false_eq:
  -- T true (fun _ ↦ ¬¬False) = T true (fun _ ↦ False).
  -- Do we have a term of type T true (fun _ ↦ ¬¬False)?
  -- If we have s.t_false : T false (fun _ ↦ ¬¬¬¬False).
  -- Since ¬¬¬¬False = ¬¬False.
  -- So s.t_false has type T false (fun _ ↦ ¬¬False).
  -- Wait, then T.mk (fun _ ↦ ¬¬False) s.t_false has type T true (fun _ ↦ ¬¬¬False).
  -- That is not T true (fun _ ↦ ¬¬False).
  -- But wait!
  -- If we cast s.t_false (which has type T false (fun _ ↦ ¬¬¬¬False)) using cast_double_false (since ¬¬¬¬False = False)?
  -- Then s.t_false_cast has type T false (fun _ ↦ False).
  -- If we apply T.mk (fun _ ↦ False) s.t_false_cast, we get T true (fun _ ↦ ¬False).
  -- Still not T true (fun _ ↦ ¬¬False).

  -- Wait!
  -- What if we use cast_double_false_eq on t_false_2 : T false (fun _ ↦ ¬¬False)?
  -- No, t_false_2 is T false, not T true.
  -- But we have s.t_true : T true (fun _ ↦ ¬¬¬False).
  -- Wait, can we cast s.t_true to T true (fun _ ↦ ¬¬False)?
  -- If we can cast T true (fun _ ↦ ¬¬¬False) to T true (fun _ ↦ ¬¬False)...
  -- But ¬¬¬False = ¬False (True), and ¬¬False = False.
  -- So we cannot cast it because True is not equal to False.
  sorry
