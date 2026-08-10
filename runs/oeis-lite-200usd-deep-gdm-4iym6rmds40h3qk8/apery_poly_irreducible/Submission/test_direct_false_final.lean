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

theorem unsound_proof_of_false : False := by
  have t_1 : T 1 (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ (((p (MyProp.mk (fun _ ↦ True)) → False) → False) → False) → False) := @T.mk 0 (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ (((p (MyProp.mk (fun _ ↦ True)) → False) → False) → False) → False) T.base_1
  have t_2 : T 1 (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ p (MyProp.mk (fun _ ↦ True)) → False) := @T.mk 0 (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ p (MyProp.mk (fun _ ↦ True)) → False) T.base_2
  cases t_1 with
  | mk a1 t_0 =>
    cases t_2 with
    | mk a2 t_0' =>
      cases t_0 with
      | base_1 =>
        cases t_0' with
        | base_2 =>
          -- Here we should have base_1 and base_2!
          -- Wait, what if t_0' is base_1?
          -- Let's see: can we prove False for all cases?
          sorry
        | base_1 =>
          sorry
      | base_2 =>
        sorry

#print axioms unsound_proof_of_false
