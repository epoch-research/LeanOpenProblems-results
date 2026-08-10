import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (α → Prop) → Prop
| base : T PUnit.{1} (fun _ ↦ True)
| mk : {α : Type} → (a : (α → Prop) → Prop) → T α (fun _ ↦ a (fun _ ↦ True)) → T (α → Prop) a

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

theorem nonempty_of_T {α : Type} {a : α → Prop} (t : T α a) : Nonempty α := by
  induction t with
  | base => exact ⟨PUnit.unit⟩
  | mk a' t_1 ih => exact ⟨fun _ ↦ True⟩

theorem unsound {β : Type} {a : β → Prop} (t : T β a) {α : Type} (h : β = (α → Prop)) : a (cast h.symm (fun _ ↦ True)) := by
  induction t with
  | base =>
    -- here β = PUnit
    -- h : PUnit = (α → Prop)
    -- This is a contradiction!
    have h_nonempty : Nonempty (α → Prop) := ⟨fun _ ↦ True⟩
    have h_nonempty_α : Nonempty α := ⟨Classical.choice h_nonempty PUnit.unit⟩
    have h_false : False := any_step_not_eq_punit α h_nonempty_α h.symm
    exact h_false.elim
  | mk a' t_1 ih =>
    -- here β = (γ → Prop)
    -- h : (γ → Prop) = (α → Prop)
    -- Since we have h, can we cast?
    sorry
