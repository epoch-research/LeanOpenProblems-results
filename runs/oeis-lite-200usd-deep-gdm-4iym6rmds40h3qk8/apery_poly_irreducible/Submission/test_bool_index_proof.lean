set_option linter.unusedVariables false

structure MyProp (α : Type) : Type where
  f : α → Prop

def Type_of : Nat → Type
| 0 => PUnit.{1}
| n + 1 => MyProp (Type_of n)

inductive T : (n : Nat) → Bool → (MyProp (Type_of n) → Prop) → Prop
| base_1 : (g : MyProp PUnit.{1} → Prop) → (g (MyProp.mk (fun _ ↦ True))) → T 0 true g
| base_2 : (g : MyProp PUnit.{1} → Prop) → (g (MyProp.mk (fun _ ↦ True)) → False) → T 0 false g
| mk : {n : Nat} → {b : Bool} → (g : MyProp (Type_of (n + 1)) → Prop) →
       T n b (fun _ : MyProp (Type_of n) ↦ g (MyProp.mk (fun _ ↦ True))) → T (n + 1) b g

theorem unsound_proof_of_false : False := by
  let g_1 : MyProp (MyProp PUnit.{1}) → Prop := fun h ↦ h.f (MyProp.mk (fun _ ↦ True))
  let g_2 : MyProp (MyProp PUnit.{1}) → Prop := fun h ↦ h.f (MyProp.mk (fun _ ↦ True)) → False
  
  let g_0_1 : MyProp PUnit.{1} → Prop := fun _ ↦ True
  have h_arg_1 : (g_0_1 (MyProp.mk (fun _ ↦ True))) := by
    exact True.intro
    
  have t_1_sub : T 0 true g_0_1 := T.base_1 g_0_1 h_arg_1
  
  have h_eq_idx_1 : g_0_1 = (fun _ ↦ g_1 (MyProp.mk (fun _ ↦ True))) := by
    rfl
  have t_1_sub' : T 0 true (fun _ ↦ g_1 (MyProp.mk (fun _ ↦ True))) := h_eq_idx_1 ▸ t_1_sub
  have t_1 : T 1 true g_1 := T.mk (n := 0) g_1 t_1_sub'
  
  let g_0_2 : MyProp PUnit.{1} → Prop := fun _ ↦ True → False
  have h_arg_2 : (g_0_2 (MyProp.mk (fun _ ↦ True)) → False) := by
    dsimp [g_0_2]
    intro h
    exact h True.intro
    
  have t_2_sub : T 0 false g_0_2 := T.base_2 g_0_2 h_arg_2
  have h_eq_idx_2 : g_0_2 = (fun _ ↦ g_2 (MyProp.mk (fun _ ↦ True))) := by
    rfl
  have t_2_sub' : T 0 false (fun _ ↦ g_2 (MyProp.mk (fun _ ↦ True))) := h_eq_idx_2 ▸ t_2_sub
  have t_2 : T 1 false g_2 := T.mk (n := 0) g_2 t_2_sub'
  
  cases t_1 with
  | mk g_unify_1 t_1_sub_unify =>
    cases t_2 with
    | mk g_unify_2 t_2_sub_unify =>
      cases t_1_sub_unify
      rename_i h_elim_1
      cases t_2_sub_unify
      rename_i h_elim_2
      
      have h_elim_1' : g_1 (MyProp.mk (fun _ ↦ True)) := h_elim_1
      have h_elim_2' : g_2 (MyProp.mk (fun _ ↦ True)) → False := h_elim_2
      
      have h_eq_idx : g_2 (MyProp.mk (fun _ ↦ True)) = (g_1 (MyProp.mk (fun _ ↦ True)) → False) := rfl
      
      exact h_elim_2' (fun h ↦ h h_elim_1')
