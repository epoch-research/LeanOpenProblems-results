set_option linter.unusedVariables false

structure MyProp (α : Type) : Type where
  f : α → Prop

def Type_of : Nat → Type
| 0 => PUnit.{1}
| n + 1 => MyProp (Type_of n)

inductive T : (n : Nat) → Bool → ((MyProp (Type_of n) → Prop) → Prop) → Prop
| base_1 : (g : MyProp PUnit.{1} → Prop) → ((g ⟨fun _ ↦ True⟩ → False) → False) → T 0 true (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False)
| base_2 : (g : MyProp PUnit.{1} → Prop) → (g ⟨fun _ ↦ True⟩ → False) → T 0 false (fun g ↦ g ⟨fun _ ↦ True⟩ → False)
| mk : {n : Nat} → {b : Bool} → (a : (MyProp (Type_of (n + 1)) → Prop) → Prop) → T n b (fun g ↦ a (fun _ ↦ g ⟨fun _ ↦ True⟩)) → T (n + 1) b a

theorem index_eq_1 (t : T 0 true (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False)) :
    (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False) = (fun g : MyProp PUnit.{1} → Prop ↦ (g ⟨fun _ ↦ True⟩ → False) → False) := by
  cases t with
  | base_1 g h => rfl

theorem index_eq_2 (t : T 0 false (fun g ↦ g ⟨fun _ ↦ True⟩ → False)) :
    (fun g ↦ g ⟨fun _ ↦ True⟩ → False) = (fun g : MyProp PUnit.{1} → Prop ↦ g ⟨fun _ ↦ True⟩ → False) := by
  cases t with
  | base_2 g h => rfl

def base_1_elim : T 0 true (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False) → (g : MyProp PUnit.{1} → Prop) → ((g ⟨fun _ ↦ True⟩ → False) → False)
| T.base_1 g h => fun g' ↦ h

def base_2_elim : T 0 false (fun g ↦ g ⟨fun _ ↦ True⟩ → False) → (g : MyProp PUnit.{1} → Prop) → (g ⟨fun _ ↦ True⟩ → False)
| T.base_2 g h => fun g' ↦ h

theorem unsound_proof_of_false : False := by
  have t_1 : T 1 true (fun p ↦ (p ⟨fun _ ↦ True⟩ → False) → False) := T.mk (fun p ↦ (p ⟨fun _ ↦ True⟩ → False) → False) (T.base_1 (fun _ ↦ True) (fun h ↦ h True.intro))
  have t_2 : T 1 false (fun p ↦ p ⟨fun _ ↦ True⟩ → False) := T.mk (fun p ↦ p ⟨fun _ ↦ True⟩ → False) (T.base_2 (fun _ ↦ False) (fun x ↦ x))
  match t_1, t_2 with
  | @T.mk n1 b1 a1 t_1_sub, @T.mk n2 b2 a2 t_2_sub =>
    have h1 : (fun g ↦ a1 (fun _ ↦ g ⟨fun _ ↦ True⟩)) = (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False) := index_eq_1 t_1_sub
    have h2 : (fun g ↦ a2 (fun _ ↦ g ⟨fun _ ↦ True⟩)) = (fun g ↦ g ⟨fun _ ↦ True⟩ → False) := index_eq_2 t_2_sub
    have t_1_sub_cast : T 0 true (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False) := cast (congrArg (T 0 true) h1) t_1_sub
    have t_2_sub_cast : T 0 false (fun g ↦ g ⟨fun _ ↦ True⟩ → False) := cast (congrArg (T 0 false) h2) t_2_sub
    have elim1 : (g : MyProp PUnit.{1} → Prop) → ((g ⟨fun _ ↦ True⟩ → False) → False) := base_1_elim t_1_sub_cast
    have elim2 : (g : MyProp PUnit.{1} → Prop) → (g ⟨fun _ ↦ True⟩ → False) := base_2_elim t_2_sub_cast
    have g_val : MyProp PUnit.{1} → Prop := fun _ ↦ False
    exact (elim1 g_val) (elim2 g_val)

#print axioms unsound_proof_of_false
