import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

structure MyProp (α : Type) : Type where
  f : α → Prop

def Type_of : Nat → Type
| 0 => PUnit.{1}
| n + 1 => MyProp (Type_of n)

inductive T : (n : Nat) → ((MyProp (Type_of n) → Prop) → Prop) → Prop
| base : T 0 (fun g ↦ g ⟨fun _ ↦ True⟩)
| mk : {n : Nat} → (a : (MyProp (Type_of (n + 1)) → Prop) → Prop) → T n (fun g ↦ a (fun _ ↦ g ⟨fun _ ↦ True⟩)) → T (n + 1) a

theorem index_eq {a : (MyProp (Type_of 0) → Prop) → Prop} (t : T 0 a) : a = (fun g ↦ g ⟨fun _ ↦ True⟩) := by
  cases t with
  | base => rfl

def bad_direct {a} (t : T 1 a) (h : a (fun _ ↦ False)) : False := by
  match t with
  | T.mk a' t_1 =>
    have h_eq_idx : (fun g : MyProp PUnit → Prop ↦ a' (fun _ ↦ g ⟨fun _ ↦ True⟩)) = (fun g : MyProp PUnit → Prop ↦ g ⟨fun _ ↦ True⟩) := index_eq t_1
    have h_eval : a' (fun _ ↦ False) = False := congrFun h_eq_idx (fun _ ↦ False)
    exact h_eval ▸ h

theorem unsound_proof_of_false : False := by
  have t_1 : T 1 (fun p ↦ p ⟨fun _ ↦ True⟩) := T.mk (fun p ↦ p ⟨fun _ ↦ True⟩) T.base
  have h_arg : (fun p : MyProp (MyProp PUnit.{1}) → Prop ↦ p ⟨fun _ ↦ True⟩) (fun _ ↦ False) := by
    dsimp
  exact bad_direct t_1 h_arg
