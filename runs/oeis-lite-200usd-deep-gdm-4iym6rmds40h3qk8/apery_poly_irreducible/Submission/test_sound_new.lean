import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → ((α → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun g ↦ g PUnit.unit)
| cheat : T PUnit.{1} (fun g ↦ g PUnit.unit) → T (PUnit.{1} → Prop) (fun g ↦ False)

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

def bad_general {α} {a} (t : T α a) (h_eq : α = (PUnit.{1} → Prop)) (h_a : a = h_eq ▸ (fun g ↦ False)) : False := by
  cases t with
  | base =>
    have h_nonempty : Nonempty PUnit.{1} := ⟨PUnit.unit⟩
    exact any_step_not_eq_punit PUnit.{1} h_nonempty h_eq.symm
  | cheat t_1 =>
    exact cantor_diagonal (PUnit.{1} → Prop) h_eq

def my_false : False := by
  have t_cheat : T (PUnit.{1} → Prop) (fun g ↦ False) := T.cheat T.base
  exact bad_general t_cheat rfl rfl
