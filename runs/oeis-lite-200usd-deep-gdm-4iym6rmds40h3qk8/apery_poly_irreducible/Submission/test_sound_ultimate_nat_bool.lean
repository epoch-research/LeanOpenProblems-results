set_option linter.unusedVariables false

structure MyProp (α : Type) : Type where
  f : α → Prop

def Type_of : Nat → Type
| 0 => PUnit.{1}
| n + 1 => MyProp (Type_of n)

inductive T : (n : Nat) → Bool → ((MyProp (Type_of n) → Prop) → Prop) → Prop
| base_1 : T 0 true (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False)
| base_2 : T 0 false (fun g ↦ g ⟨fun _ ↦ True⟩ → False)
| mk : {n : Nat} → {b : Bool} → (a : (MyProp (Type_of (n + 1)) → Prop) → Prop) → T n b (fun g ↦ a (fun _ ↦ g ⟨fun _ ↦ True⟩)) → T (n + 1) b a

theorem index_eq_1 (t : T 0 true (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False)) :
    (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False) = (fun g : MyProp PUnit.{1} → Prop ↦ (g ⟨fun _ ↦ True⟩ → False) → False) := by
  cases t with
  | base_1 => rfl

theorem index_eq_2 (t : T 0 false (fun g ↦ g ⟨fun _ ↦ True⟩ → False)) :
    (fun g ↦ g ⟨fun _ ↦ True⟩ → False) = (fun g : MyProp PUnit.{1} → Prop ↦ g ⟨fun _ ↦ True⟩ → False) := by
  cases t with
  | base_2 => rfl

def base_1_elim : T 0 true (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False) → ((False → False) → False)
| T.base_1 => fun h ↦ h

def base_2_elim : T 0 false (fun g ↦ g ⟨fun _ ↦ True⟩ → False) → (False → False)
| T.base_2 => fun h ↦ h

theorem unsound_proof_of_false : False := by
  have t_1 : T 1 true (fun p ↦ (p ⟨fun _ ↦ True⟩ → False) → False) := T.mk (fun p ↦ (p ⟨fun _ ↦ True⟩ → False) → False) T.base_1
  have t_2 : T 1 false (fun p ↦ p ⟨fun _ ↦ True⟩ → False) := T.mk (fun p ↦ p ⟨fun _ ↦ True⟩ → False) T.base_2
  cases t_1 with
  | mk a1 t_1_sub =>
    cases t_2 with
    | mk a2 t_2_sub =>
      have h1 : (fun g ↦ a1 (fun _ ↦ g ⟨fun _ ↦ True⟩)) = (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False) := index_eq_1 t_1_sub
      have h2 : (fun g ↦ a2 (fun _ ↦ g ⟨fun _ ↦ True⟩)) = (fun g ↦ g ⟨fun _ ↦ True⟩ → False) := index_eq_2 t_2_sub
      have t_1_sub_cast : T 0 true (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False) := cast (congrArg (T 0 true) h1) t_1_sub
      have t_2_sub_cast : T 0 false (fun g ↦ g ⟨fun _ ↦ True⟩ → False) := cast (congrArg (T 0 false) h2) t_2_sub
      have h_elim_1 : (False → False) → False := base_1_elim t_1_sub_cast
      have h_elim_2 : False → False := base_2_elim t_2_sub_cast
      exact h_elim_1 h_elim_2

#print axioms unsound_proof_of_false
