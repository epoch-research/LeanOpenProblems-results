import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → ((List α → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun g ↦ g [])
| mk : {α : Type} → (a : (List (List α) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ g [])) → T (List α) a

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

theorem nonempty_of_T {α : Type} {a : (((α → Prop) → Prop) → Prop)} (t : T α a) : Nonempty α := by
  induction t with
  | base => exact ⟨PUnit.unit⟩
  | mk a' t_1 ih => exact ⟨fun _ ↦ True⟩

def bad {α} {a : (((α → Prop) → Prop) → Prop)} (t : T α a) (h_eq : α = PUnit.{1}) (h : a (fun _ ↦ False)) : False := by
  induction t with
  | base =>
    exact h True.intro
  | mk a' t_1 ih =>
    have h_nonempty : Nonempty _ := nonempty_of_T t_1
    have h_false : False := any_step_not_eq_punit _ h_nonempty h_eq
    exact h_false.elim

theorem unsound_proof_of_false : False := by
  have t_1 : T (PUnit.{1} → Prop) (fun H ↦ H (fun _ ↦ True) → False) := T.mk (fun H ↦ H (fun _ ↦ True) → False) T.base
  cases t_1 with
  | mk a' t_0 =>
    -- Let's see what we can do in this case!
    sorry
