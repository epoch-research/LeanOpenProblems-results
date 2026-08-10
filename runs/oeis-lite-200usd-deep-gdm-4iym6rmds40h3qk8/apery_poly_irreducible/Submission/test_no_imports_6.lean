set_option linter.unusedVariables false

inductive T : (α : Type) → ((List α → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun g ↦ g [])
| mk : {α : Type} → (a : (List (List α) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ g [])) → T (List α) a

theorem cast_symm_cast {α β : Type} (h : α = β) (x : α) : cast h.symm (cast h x) = x := by
  cases h
  rfl

theorem nonempty_of_T {α : Type} {a : (List α → Prop) → Prop} (t : T α a) : Nonempty α := by
  induction t with
  | base => exact ⟨PUnit.unit⟩
  | mk a' t_1 ih => exact ⟨[]⟩

theorem any_step_not_eq_punit (α : Type) (h_nonempty : Nonempty α) (h : List α = PUnit.{1}) : False := by
  have x := Classical.choice h_nonempty
  have h_eq : cast h [] = cast h [x] := Subsingleton.elim _ _
  have h_empty_eq : [] = [x] := by
    have h1 := (cast_symm_cast h []).symm
    have h2 := cast_symm_cast h [x]
    have h3 := congrArg (cast h.symm) h_eq
    exact h1.trans (h3.trans h2)
  cases h_empty_eq

theorem index_eq {α} {a : (List α → Prop) → Prop} (t : T α a) (h : α = PUnit.{1}) : a = h ▸ (fun g : List PUnit.{1} → Prop ↦ g []) := by
  cases t with
  | base => rfl
  | mk a' t_1 =>
    have h_nonempty : Nonempty _ := nonempty_of_T t_1
    have h_false : False := any_step_not_eq_punit _ h_nonempty h
    exact h_false.elim

def bad_direct {α : Type} {a} (t : T α a) (h_eq : α = List PUnit.{1}) (h : a (fun _ ↦ False)) : False := by
  cases t with
  | base =>
    have h_nonempty : Nonempty PUnit.{1} := ⟨PUnit.unit⟩
    have h_false : False := any_step_not_eq_punit PUnit.{1} h_nonempty h_eq.symm
    exact h_false.elim
  | @mk α_1 a' t_1 =>
    have h_eq_unify : α_1 = PUnit.{1} := by
      cases h_eq
      rfl
    cases h_eq_unify
    have h_eq_idx : (fun g ↦ a' (fun _ ↦ g [])) = (fun g ↦ g []) := index_eq t_1 rfl
    have h_eval := congrFun h_eq_idx (fun _ ↦ False)
    exact h_eval ▸ h

theorem unsound_proof_of_false : False := by
  have t_1 : T (List PUnit.{1}) (fun p ↦ p []) := T.mk (fun p ↦ p []) T.base
  have h_arg : (fun p : List (List PUnit.{1}) → Prop ↦ p []) (fun _ ↦ False) := by
    dsimp
  exact bad_direct t_1 rfl h_arg

#print axioms unsound_proof_of_false
