import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → ((α → Prop) → Prop) → Prop
| base : T PUnit (fun g ↦ g PUnit.unit)
| mk : {α : Type} → (a : ((α → Prop) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ True)) → T (α → Prop) a

theorem cast_symm_cast {α β : Type} (h : α = β) (x : α) : cast h.symm (cast h x) = x := by
  cases h
  rfl

theorem any_step_not_eq_punit (α : Type) (h_nonempty : Nonempty α) : ((α → Prop) = PUnit) → False := fun h ↦ by
  have h_eq : (fun _ : α ↦ True) = (fun _ : α ↦ False) := by
    have h_eq_punit : cast h (fun _ : α ↦ True) = cast h (fun _ : α ↦ False) := Subsingleton.elim _ _
    have h1 := (cast_symm_cast h (fun _ : α ↦ True)).symm
    have h2 := cast_symm_cast h (fun _ : α ↦ False)
    have h3 := congrArg (cast h.symm) h_eq_punit
    exact h1.trans (h3.trans h2)
  have x := Classical.choice h_nonempty
  have h_true_eq_false : True = False := congrFun h_eq x
  exact h_true_eq_false.mp True.intro

theorem nonempty_of_T {α : Type} {a : (α → Prop) → Prop} (t : T α a) : Nonempty α := by
  induction t with
  | base => exact ⟨PUnit.unit⟩
  | mk a' t_1 ih => exact ⟨fun _ ↦ True⟩

theorem index_eq {α} {a : (α → Prop) → Prop} (t : T α a) (h : α = PUnit) : a = h ▸ (fun g : PUnit → Prop ↦ g PUnit.unit) := by
  cases t with
  | base => rfl
  | mk a' t_1 =>
    have h_nonempty : Nonempty _ := nonempty_of_T t_1
    have h_false : False := any_step_not_eq_punit _ h_nonempty h
    exact h_false.elim

theorem unsound {α : Type} {a : (α → Prop) → Prop} (t : T α a) : a (fun _ ↦ True) := by
  induction t with
  | base => exact True.intro
  | mk a' t_1 ih => exact ih

def bad_direct {α} {a} (t : T α a) (h_eq : α = (PUnit → Prop)) : False := by
  cases t with
  | base =>
    have h_nonempty : Nonempty PUnit := ⟨PUnit.unit⟩
    exact any_step_not_eq_punit PUnit h_nonempty h_eq.symm
  | mk a' t_1 =>
    cases h_eq
    have h_eq_idx : (fun g : PUnit → Prop ↦ a' (fun _ ↦ True)) = (fun g ↦ g PUnit.unit) := index_eq t_1 rfl
    have h_eval := congrFun h_eq_idx (fun _ ↦ False)
    have h_eval_simp : a' (fun _ ↦ True) = False := h_eval
    have h_true : a' (fun _ ↦ True) := unsound t_1
    exact h_eval_simp ▸ h_true

theorem unsound_proof_of_false : False := by
  have t_false : T (PUnit → Prop) (fun _ ↦ False) := T.mk (fun _ ↦ False) T.base
  exact bad_direct t_false rfl
