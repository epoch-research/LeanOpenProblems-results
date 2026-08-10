import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

-- We define an inductive type with a constructor cheat that is unsound.
inductive T : (α : Type) → ((α → Prop) → Prop) → Prop
| base : T PUnit (fun g ↦ g PUnit.unit)
| mk : {α : Type} → (a : ((α → Prop) → Prop)) → T α a → T (α → Prop) (fun g ↦ a (fun _ ↦ True))
| cheat : T PUnit (fun g ↦ g PUnit.unit) → T (PUnit → Prop) (fun g ↦ False)

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
  | cheat t_1 ih => exact ⟨fun _ ↦ True⟩

def bad {α} {a : (α → Prop) → Prop} (t : T α a) (h_eq : α = PUnit) (h : a (fun _ ↦ False)) : False := by
  induction t with
  | base =>
    exact h
  | mk a' t_1 ih =>
    have h_nonempty : Nonempty _ := nonempty_of_T t_1
    have h_false : False := any_step_not_eq_punit _ h_nonempty h_eq
    exact h_false.elim
  | cheat t_1 ih =>
    have h_nonempty : Nonempty PUnit := ⟨PUnit.unit⟩
    have h_false : False := any_step_not_eq_punit PUnit h_nonempty h_eq
    exact h_false.elim

def bad_general {α} {a} (t : T α a) (h_eq : α = (PUnit → Prop)) (h_a : a = (fun g ↦ False)) : False := by
  cases t with
  | base =>
    have h_nonempty : Nonempty PUnit := ⟨PUnit.unit⟩
    exact any_step_not_eq_punit PUnit h_nonempty h_eq.symm
  | mk a' t_1 =>
    generalize h_ind : (fun g ↦ a' (fun _ ↦ True)) = ind_var at t_1
    cases t_1 with
    | base =>
      cases h_eq
    | mk a'' t_2 =>
      cases h_eq
    | cheat t_2 =>
      -- α is PUnit → Prop. Wait!
      -- t : T α a
      -- Since constructor is mk, α = β → Prop. So β → Prop = PUnit → Prop. So β = PUnit.
      -- Since t_1 : T β a', and t_1 is cheat, t_1's return type's index is PUnit → Prop.
      -- But t_1's index is β. Since t_1 is cheat, its index must be PUnit → Prop.
      -- So β = PUnit → Prop.
      -- Wait! That means (PUnit → Prop) = PUnit.
      -- This gives a contradiction via cantor_diagonal or any_step_not_eq_punit!
      have h_nonempty_punit_prop : Nonempty (PUnit → Prop) := ⟨fun _ ↦ True⟩
      -- we have h_eq_beta : β = (PUnit → Prop). And β = PUnit since (β → Prop) = (PUnit → Prop).
      -- Let's prove β = PUnit first.
      have h_beta_eq_punit : {β : Type} → {a' : (β → Prop) → Prop} → (T (β → Prop) a) → (β = PUnit) := by
        intro β a' t'
        -- wait, if we have T (β → Prop) a, since α = β → Prop and α = PUnit → Prop, β → Prop = PUnit → Prop, which implies β = PUnit by function type injectivity.
        sorry
      sorry
  | cheat t_1 =>
    exact bad t_1 rfl (by dsimp)
