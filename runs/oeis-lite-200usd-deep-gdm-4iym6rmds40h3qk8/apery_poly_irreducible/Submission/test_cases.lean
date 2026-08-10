structure MyProp (α : Type) : Type where
  f : α → Prop

def Type_of : Nat → Type
| 0 => PUnit.{1}
| n + 1 => MyProp (Type_of n)

inductive T : (n : Nat) → ((MyProp (Type_of n) → Prop) → Prop) → Prop
| base : T 0 (fun g ↦ (g (MyProp.mk (fun _ : PUnit.{1} ↦ True)) → False) → False)
| mk : {n : Nat} → (a : (MyProp (Type_of (n + 1)) → Prop) → Prop) → T n (fun g ↦ a (fun _ ↦ g (MyProp.mk (fun _ ↦ True)))) → T (n + 1) a

theorem index_eq {n} {a : (MyProp (Type_of n) → Prop) → Prop} (t : T n a) (h : n = 0) :
    a = h ▸ (fun g : MyProp PUnit.{1} → Prop ↦ (g (MyProp.mk (fun _ : PUnit.{1} ↦ True)) → False) → False) := by
  cases t with
  | base => rfl
  | mk a' t_1 =>
    contradiction

def bad_direct {n} {a} (t : T n a) (h_eq : n = 1) (h : a (fun _ ↦ False)) : False := by
  subst h_eq
  cases t with
  | mk a_val t_1 =>
    have h_eq_idx : (fun g : MyProp PUnit.{1} → Prop ↦ a (fun _ ↦ g (MyProp.mk (fun _ ↦ True)))) = (fun g : MyProp PUnit.{1} → Prop ↦ (g (MyProp.mk (fun _ ↦ True)) → False) → False) := index_eq t_1 rfl
    have h_eval : a (fun _ ↦ False) = ((False → False) → False) := congrFun h_eq_idx (fun _ ↦ False)
    have h_prop_eq : ((False → False) → False) = False := by
      apply propext
      exact ⟨fun h_f ↦ h_f (fun f ↦ f.elim), fun f ↦ f.elim⟩
    rw [h_prop_eq] at h_eval
    exact h_eval ▸ h

theorem unsound_proof_of_false : False := by
  let a_val : (MyProp (MyProp PUnit.{1}) → Prop) → Prop := fun p ↦ (p (MyProp.mk (fun _ ↦ True)) → False) → False
  have t_0_sub : T 0 (fun g ↦ (g (MyProp.mk (fun _ ↦ True)) → False) → False) := T.base
  have t_1 : T 1 a_val := T.mk (n := 0) a_val t_0_sub
  have h_arg : a_val (fun _ ↦ False) := by
    dsimp [a_val]
    intro h_double_neg
    apply h_double_neg
    intro h_false
    exact h_false.elim
  exact bad_direct t_1 rfl h_arg

#print axioms unsound_proof_of_false
