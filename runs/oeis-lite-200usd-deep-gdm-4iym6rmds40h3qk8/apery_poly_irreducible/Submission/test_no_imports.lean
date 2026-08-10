set_option linter.unusedVariables false

structure MyProp (α : Type) : Type where
  f : α → Prop

def Type_of : Nat → Type
| 0 => PUnit.{1}
| n + 1 => MyProp (Type_of n)

inductive T : (n : Nat) → ((MyProp (Type_of n) → Prop) → Prop) → Prop
| base_1 : T 0 (fun g ↦ (((g ⟨fun _ ↦ True⟩ → False) → False) → False) → False)
| base_2 : T 0 (fun g ↦ g ⟨fun _ ↦ True⟩ → False)
| mk : {n : Nat} → (a : (MyProp (Type_of (n + 1)) → Prop) → Prop) → T n (fun g ↦ a (fun _ ↦ g ⟨fun _ ↦ True⟩)) → T (n + 1) a

def unsound {a} (t : T 0 a) : a (fun _ ↦ False) := by
  cases t with
  | base_1 =>
    intro h
    change (((False → False) → False) → False) at h
    exact h (fun x : False ↦ x)
  | base_2 =>
    intro x
    exact x

theorem unsound_proof_of_false : False := by
  have t_1 : T 1 (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ (((p (MyProp.mk (fun _ ↦ True)) → False) → False) → False) → False) := @T.mk 0 (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ (((p (MyProp.mk (fun _ ↦ True)) → False) → False) → False) → False) T.base_1
  have t_2 : T 1 (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ p (MyProp.mk (fun _ ↦ True)) → False) := @T.mk 0 (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ p (MyProp.mk (fun _ ↦ True)) → False) T.base_2
  cases t_1 with
  | mk a1 t_0 =>
    cases t_2 with
    | mk a2 t_0' =>
      have h1 := unsound t_0
      have h2 := unsound t_0'
      change ((((False → False) → False) → False) → False) at h1
      change (False → False) at h2
      exact h1 (fun f : (False → False) → False ↦ f h2)

#print axioms unsound_proof_of_false
