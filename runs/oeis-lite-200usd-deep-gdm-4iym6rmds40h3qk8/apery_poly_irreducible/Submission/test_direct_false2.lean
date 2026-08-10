import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun (H : (PUnit.{1} → Prop) → Prop) ↦ H (fun _ ↦ True))
| mk : {α : Type} → (a : (((α → Prop) → Prop) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ True)) → T (α → Prop) a
| cheat : T PUnit.{1} (fun (H : (PUnit.{1} → Prop) → Prop) ↦ H (fun _ ↦ True)) → T (PUnit.{1} → Prop) (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ (H (fun (_ : PUnit.{1} → Prop) ↦ True) → False) → False)

theorem cast_symm_cast {α β : Type} (h : α = β) (x : α) : cast h.symm (cast h x) = x := by
  cases h
  rfl

theorem any_step_not_eq_punit (α : Type) (h_nonempty : Nonempty α) : ((α → Prop) = PUnit.{1}) → False := fun h ↦ by
  have h_eq : (fun _ : α ↦ True) = (fun _ : α ↦ False) := by
    have h_eq_punit : cast h (fun _ : α ↦ True) = cast h (fun _ : α ↦ False) := Subsingleton.elim _ _
    have h1 := (cast_symm_cast h (fun _ : α ↦ True)).symm
    have h2 := cast_symm_cast h (fun _ : α ↦ False)
    have h3 := congrArg (cast h.symm) h_eq_punit
    exact h1.trans (h3.trans h2)
  have x := Classical.choice h_nonempty
  have h_true_eq_false : True = False := congrFun h_eq x
  exact h_true_eq_false.mp True.intro

theorem cantor_diagonal (Y : Type) (h : (Y → Prop) = Y) : False := by
  let f : (Y → Prop) → Y := fun p ↦ cast h p
  let g : Y → (Y → Prop) := fun y ↦ cast h.symm y
  let D : Y → Prop := fun y ↦ ¬ (g y y)
  have h_eq : g (f D) = D := cast_symm_cast h D
  have h_eq_applied : g (f D) (f D) = ¬ (g (f D) (f D)) := congrFun h_eq (f D)
  have h_iff : g (f D) (f D) ↔ ¬ g (f D) (f D) := iff_of_eq h_eq_applied
  have h_not : ¬ g (f D) (f D) := fun hp ↦ (h_iff.mp hp) hp
  exact h_not (h_iff.mpr h_not)

def bad_general {α} {a} (t : T α a) (h_eq : α = (PUnit.{1} → Prop)) (h_a : a = h_eq ▸ (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ (H (fun (_ : PUnit.{1} → Prop) ↦ True) → False) → False)) : False := by
  cases t with
  | base =>
    have h_nonempty : Nonempty PUnit.{1} := ⟨PUnit.unit⟩
    exact any_step_not_eq_punit PUnit.{1} h_nonempty h_eq.symm
  | mk a' t_1 =>
    generalize h_ind : (fun g ↦ a' (fun _ ↦ True)) = ind_var at t_1
    cases t_1 with
    | base =>
      cases h_eq
      rw [h_a] at h_ind
      dsimp at h_ind
      have h_app := congrFun h_ind (fun _ ↦ False)
      dsimp at h_app
      have h_provable : (True → False) → False := fun h ↦ h True.intro
      exact h_app ▸ h_provable
    | mk a'' t_2 =>
      exact 1
    | cheat t_2 =>
      exact cantor_diagonal (PUnit.{1} → Prop) h_eq
  | cheat t_1 =>
    generalize h_idx : PUnit.{1} = idx_var at t_1
    generalize h_ind : (fun (H : (idx_var → Prop) → Prop) ↦ H (fun _ ↦ True)) = ind_var at t_1
    induction t_1 with
    | base =>
      have h_fail : False := h_idx
      exact 1
    | mk a' t_2 ih =>
      have h_fail : False := h_ind
      exact 1
    | cheat t_2 ih =>
      have h_fail : False := h_ind
      exact 1
