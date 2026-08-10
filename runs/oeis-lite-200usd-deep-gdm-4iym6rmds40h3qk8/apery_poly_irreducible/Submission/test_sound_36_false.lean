import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → ((α → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun g ↦ g PUnit.unit)
| mk : {α : Type} → (a : ((α → Prop) → Prop)) → T α a → T (α → Prop) (fun g ↦ a (fun _ ↦ True))
| cheat : T (PUnit.{1} → Prop) (fun g ↦ False)

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
  | mk a' t_1 ih => exact ⟨fun _ ↦ True⟩
  | cheat => exact ⟨fun _ ↦ True⟩

def bad2 (α : Type) (a : (α → Prop) → Prop) (t : T α a) (h_eq : α = PUnit.{1}) (h_a : a (fun _ ↦ False)) : False := by
  induction t with
  | base =>
    exact h_a
  | mk a' t_1 ih =>
    have h_nonempty : Nonempty _ := nonempty_of_T t_1
    have h_false : False := any_step_not_eq_punit _ h_nonempty h_eq
    exact h_false.elim
  | cheat =>
    have h_nonempty : Nonempty (PUnit.{1} → Prop) := ⟨fun _ ↦ True⟩
    have h_false : False := any_step_not_eq_punit _ h_nonempty h_eq
    exact h_false.elim

theorem unsound_proof_of_false : False := by
  have t_cheat : T (PUnit.{1} → Prop) (fun g ↦ False) := T.cheat
  generalize h_eq : (PUnit.{1} → Prop) = α at t_cheat
  generalize h_a : (fun g ↦ False) = a at t_cheat
  induction t_cheat with
  | base =>
    -- α is PUnit.{1}, but h_eq is (PUnit.{1} → Prop) = PUnit.{1}
    have h_nonempty : Nonempty PUnit.{1} := ⟨PUnit.unit⟩
    have h_false : False := any_step_not_eq_punit PUnit.{1} h_nonempty h_eq
    exact h_false.elim
  | mk a' t_1 ih =>
    -- α is β → Prop, but h_eq is (PUnit.{1} → Prop) = (β → Prop)
    -- So β = PUnit.{1}.
    -- We have h_a : (fun g ↦ False) = (fun g ↦ a' (fun _ ↦ True))
    -- So a' (fun _ ↦ True) = False.
    -- Wait! ih has type:
    -- ((PUnit.{1} → Prop) = β) → ((fun g ↦ False) = a') → False.
    -- But we have h_eq : (PUnit.{1} → Prop) = (β → Prop).
    -- So we cannot apply ih.
    sorry
  | cheat =>
    -- α is PUnit.{1} → Prop, and a is fun g ↦ False.
    -- h_a has type (fun g ↦ False) = (fun g ↦ False).
    -- Wait! The cheat constructor has no induction hypotheses, but does it give us anything?
    -- No, it's just a constructor with no arguments.
    sorry
