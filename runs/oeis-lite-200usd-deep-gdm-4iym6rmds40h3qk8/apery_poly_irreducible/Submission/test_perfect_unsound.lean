import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

structure MyProp (α : Type) : Type where
  f : α → Prop

def Type_of : Nat → Type
| 0 => PUnit.{1}
| n + 1 => MyProp (Type_of n)

inductive T : (n : Nat) → ((MyProp (Type_of n) → Prop) → Prop) → Prop
| base : T 0 (fun g ↦ (g ⟨fun _ ↦ True⟩ → False) → False)
| mk : {n : Nat} → (a : (MyProp (Type_of (n + 1)) → Prop) → Prop) → T n (fun g ↦ a (fun _ ↦ g ⟨fun _ ↦ True⟩)) → T (n + 1) a

theorem unsound {a} (t : T 0 a) : a (fun _ ↦ False) := by
  cases t with
  | base =>
    exact fun h ↦ h (fun x : False ↦ x)

theorem unsound_proof_of_false : False := by
  have t_1 : T 1 (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ (p (MyProp.mk (fun _ ↦ True)) → False) → False) := @T.mk 0 (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ (p (MyProp.mk (fun _ ↦ True)) → False) → False) T.base
  cases t_1 with
  | mk a' t_0 =>
    have h_unsound := unsound t_0
    change ((False → False) → False) at h_unsound
    exact h_unsound (fun x ↦ x)








