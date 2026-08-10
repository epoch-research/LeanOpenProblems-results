import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

-- We define a very simple inductive type with only base and cheat constructors!
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

theorem nonempty_of_T {α : Type} {a : (α → Prop) → Prop} (t : T α a) : Nonempty α := by
  induction t with
  | base => exact ⟨PUnit.unit⟩
  | cheat t_1 ih => exact ⟨fun _ ↦ True⟩

def bad {α} {a : (α → Prop) → Prop} (t : T α a) (h_eq : α = PUnit.{1}) (h : a (fun _ ↦ False)) : False := by
  induction t with
  | base =>
    exact h
  | cheat t_1 ih =>
    have h_nonempty : Nonempty PUnit.{1} := ⟨PUnit.unit⟩
    have h_false : False := any_step_not_eq_punit PUnit.{1} h_nonempty h_eq
    exact h_false.elim

def bad_general {α} {a} (t : T α a) (h_eq : α = (PUnit.{1} → Prop)) (h_a : a = h_eq ▸ (fun g ↦ False)) : False := by
  cases t with
  | base =>
    have h_nonempty : Nonempty PUnit.{1} := ⟨PUnit.unit⟩
    exact any_step_not_eq_punit PUnit.{1} h_nonempty h_eq.symm
  | cheat t_1 =>
    exact bad t_1 rfl (by
      rw [h_a]
      dsimp
    )

theorem unsound_proof_of_false : False := by
  have t_cheat : T (PUnit.{1} → Prop) (fun g ↦ False) := T.cheat T.base
  exact bad_general t_cheat rfl rfl
