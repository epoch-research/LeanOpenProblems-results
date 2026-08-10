set_option linter.unusedVariables false

structure MyProp (α : Type) : Type where
  f : α → Prop

inductive T : (α : Type) → ((MyProp α → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun g ↦ g (MyProp.mk (fun _ : PUnit.{1} ↦ True)) → False)
| mk : {α : Type} → (h_nonempty : Nonempty α) → (a : (MyProp (MyProp α) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ g (MyProp.mk (fun _ : α ↦ True)))) → T (MyProp α) a

theorem any_step_not_eq_punit (α : Type) (h_nonempty : Nonempty α) (h : MyProp α = PUnit.{1}) : False := by
  have h_sub : Subsingleton (MyProp α) := h ▸ (by infer_instance : Subsingleton PUnit.{1})
  have h_eq : MyProp.mk (fun _ : α ↦ True) = MyProp.mk (fun _ : α ↦ False) := Subsingleton.elim _ _
  have h_f_eq : (fun _ : α ↦ True) = (fun _ : α ↦ False) := congrArg MyProp.f h_eq
  have x := Classical.choice h_nonempty
  have h_true_eq_false : True = False := congrFun h_f_eq x
  exact h_true_eq_false.mp True.intro

theorem nonempty_of_T {α : Type} {a : (MyProp α → Prop) → Prop} (t : T α a) : Nonempty α := by
  induction t with
  | base => exact ⟨PUnit.unit⟩
  | mk h_nonempty a' t_1 ih => exact ⟨⟨fun _ ↦ True⟩⟩

theorem index_eq {α} {a : (MyProp α → Prop) → Prop} (t : T α a) (h : α = PUnit.{1}) : a = h ▸ (fun g : MyProp PUnit.{1} → Prop ↦ g (MyProp.mk (fun _ : PUnit.{1} ↦ True)) → False) := by
  cases t with
  | base => rfl
  | mk h_nonempty a' t_1 =>
    have h_nonempty_α : Nonempty _ := nonempty_of_T t_1
    have h_false : False := any_step_not_eq_punit _ h_nonempty_α h
    exact h_false.elim

def bad_direct {α : Type} {a} (t : T α a) (h_eq : α = MyProp PUnit.{1}) (h : a (fun _ ↦ False)) : False := by
  cases t with
  | base =>
    have h_nonempty : Nonempty PUnit.{1} := ⟨PUnit.unit⟩
    have h_false : False := any_step_not_eq_punit PUnit.{1} h_nonempty h_eq.symm
    exact h_false.elim
  | mk h_nonempty a' t_1 =>
    have h_eq_unify : _ = PUnit.{1} := by
      cases h_eq
      rfl
    cases h_eq_unify
    have h_eq_idx : (fun g ↦ a' (fun _ ↦ g (MyProp.mk (fun _ : PUnit.{1} ↦ True)))) = (fun g ↦ g (MyProp.mk (fun _ : PUnit.{1} ↦ True)) → False) := index_eq t_1 rfl
    have h_eval := congrFun h_eq_idx (fun _ ↦ False)
    exact (h_eval ▸ h) (by contradiction)

theorem unsound_proof_of_false : False := by
  have h_nonempty : Nonempty PUnit.{1} := ⟨PUnit.unit⟩
  have t_1 : T (MyProp PUnit.{1}) (fun p ↦ p (MyProp.mk (fun _ : MyProp PUnit.{1} ↦ True)) → False) :=
    T.mk h_nonempty (fun p ↦ p (MyProp.mk (fun _ : MyProp PUnit.{1} ↦ True)) → False) T.base
  have h_arg : (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ p (MyProp.mk (fun _ : MyProp PUnit.{1} ↦ True)) → False) (fun _ ↦ False) := by
    dsimp
    intro h
    exact h
  exact bad_direct t_1 rfl h_arg

#print axioms unsound_proof_of_false
