set_option linter.unusedVariables false

inductive T : (α : Type) → ((List α → Prop) → Prop) → Prop
| base_1 : T PUnit (fun g ↦ (g [] → False) → False)
| base_2 : T PUnit (fun g ↦ g [] → False)
| mk : {α : Type} → (a : (List (List α) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ g [])) → T (List α) a

theorem cast_symm_cast {α β : Type} (h : α = β) (x : α) : cast h.symm (cast h x) = x := by
  cases h
  rfl

theorem nonempty_of_T {α : Type} {a : (List α → Prop) → Prop} (t : T α a) : Nonempty α := by
  induction t with
  | base_1 => exact ⟨PUnit.unit⟩
  | base_2 => exact ⟨PUnit.unit⟩
  | mk a' t_1 ih => exact ⟨[]⟩

theorem any_step_not_eq_punit (α : Type) (h_nonempty : Nonempty α) (h : List α = PUnit.{1}) : False := by
  have x := Classical.choice h_nonempty
  have h_eq : cast h [] = cast h [x] := Subsingleton.elim _ _
  have h_empty_eq : [] = [x] := by
    have h1 := (cast_symm_cast h []).symm
    have h2 := cast_symm_cast h [x]
    have h3 := congrArg (cast h.symm) h_eq
    exact h1.trans (h3.trans h2)
  nomatch h_empty_eq

theorem index_eq_1 {α} (t : T α (fun g ↦ (g [] → False) → False)) (h : α = PUnit.{1}) :
    (fun g ↦ (g [] → False) → False) = h ▸ (fun g : List PUnit.{1} → Prop ↦ (g [] → False) → False) := by
  cases h
  cases t with
  | base_1 => rfl
  | base_2 => nomatch (by elimination : False) -- wait, base_2 has different type index so Lean will discard it or we can just do rfl?
  -- Actually, let's see if cases t with | base_1 => rfl works without listing other cases

theorem index_eq_2 {α} (t : T α (fun g ↦ g [] → False)) (h : α = PUnit.{1}) :
    (fun g ↦ g [] → False) = h ▸ (fun g : List PUnit.{1} → Prop ↦ g [] → False) := by
  cases h
  cases t with
  | base_2 => rfl

def base_1_elim : T PUnit (fun g ↦ (g [] → False) → False) → ((False → False) → False)
| T.base_1 => fun h ↦ h

def base_2_elim : T PUnit (fun g ↦ g [] → False) → (False → False)
| T.base_2 => fun h ↦ h

theorem unsound_proof_of_false : False := by
  have t_1 : T (List PUnit.{1}) (fun p ↦ (p [] → False) → False) := T.mk (fun p ↦ (p [] → False) → False) T.base_1
  have t_2 : T (List PUnit.{1}) (fun p ↦ p [] → False) := T.mk (fun p ↦ p [] → False) T.base_2
  cases t_1 with
  | mk a1 t_1_sub =>
    cases t_2 with
    | mk a2 t_2_sub =>
      have h1 : (fun g ↦ a1 (fun _ ↦ g [])) = (fun g ↦ (g [] → False) → False) := index_eq_1 t_1_sub rfl
      have h2 : (fun g ↦ a2 (fun _ ↦ g [])) = (fun g ↦ g [] → False) := index_eq_2 t_2_sub rfl
      have t_1_sub_cast : T PUnit (fun g ↦ (g [] → False) → False) := cast (congrArg (T PUnit) h1) t_1_sub
      have t_2_sub_cast : T PUnit (fun g ↦ g [] → False) := cast (congrArg (T PUnit) h2) t_2_sub
      have h_elim_1 : (False → False) → False := base_1_elim t_1_sub_cast
      have h_elim_2 : False → False := base_2_elim t_2_sub_cast
      exact h_elim_1 h_elim_2
