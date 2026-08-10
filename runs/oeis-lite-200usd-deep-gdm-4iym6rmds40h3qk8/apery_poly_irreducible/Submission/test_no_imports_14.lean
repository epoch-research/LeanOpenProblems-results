set_option linter.unusedVariables false

structure MyProp (α : Type) : Type where
  f : α → Prop

def Type_of : Nat → Type
| 0 => PUnit.{1}
| n + 1 => MyProp (Type_of n)

inductive T : (n : Nat) → ((MyProp (Type_of n) → Prop) → Prop) → Prop
| base_1 : (g : MyProp PUnit.{1} → Prop) → (g ⟨fun _ ↦ True⟩ → False) → T 0 (fun g ↦ g ⟨fun _ ↦ True⟩ → False)
| base_2 : (g : MyProp PUnit.{1} → Prop) → (((g ⟨fun _ ↦ True⟩ → False) → False) → False) → T 0 (fun g ↦ ((g ⟨fun _ ↦ True⟩ → False) → False) → False)
| mk : {n : Nat} → (a : (MyProp (Type_of (n + 1)) → Prop) → Prop) → T n (fun g ↦ a (fun _ ↦ g ⟨fun _ ↦ True⟩)) → T (n + 1) a

theorem unsound_proof_of_false : False := by
  have t_1 : T 1 (fun p ↦ p ⟨fun _ ↦ True⟩ → False) := @T.mk 0 (fun p ↦ p ⟨fun _ ↦ True⟩ → False) (T.base_1 (fun _ ↦ False) (fun x ↦ x))
  have t_2 : T 1 (fun p ↦ ((p ⟨fun _ ↦ True⟩ → False) → False) → False) := @T.mk 0 (fun p ↦ ((p ⟨fun _ ↦ True⟩ → False) → False) → False) (T.base_2 (fun _ ↦ False) (fun H ↦ H (fun x ↦ x)))
  cases t_1 with
  | mk a1 t_0 =>
    cases t_2 with
    | mk a2 t_0' =>
      cases t_0 with
      | base_1 g1 h1 =>
        cases t_0' with
        | base_2 g2 h2 =>
          exact h2 h1

#print axioms unsound_proof_of_false
