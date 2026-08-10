set_option linter.unusedVariables false

def Type_of : Nat → Type
| 0 => PUnit.{1}
| n + 1 => List (Type_of n)

inductive T : (n : Nat) → Bool → ((Type_of n → Prop) → Prop) → Prop
| base_1 : (g : PUnit.{1} → Prop) → ((g PUnit.unit → False) → False) → T 0 true (fun g ↦ (g PUnit.unit → False) → False)
| base_2 : (g : PUnit.{1} → Prop) → (g PUnit.unit → False) → T 0 false (fun g ↦ g PUnit.unit → False)
| mk : {n : Nat} → {b : Bool} → (a : (Type_of (n + 1) → Prop) → Prop) → T n b (fun g ↦ a (fun _ ↦ g)) → T (n + 1) b a

theorem index_eq_1 (t : T 0 true (fun g ↦ (g PUnit.unit → False) → False)) :
    (fun g ↦ (g PUnit.unit → False) → False) = (fun g : PUnit.{1} → Prop ↦ (g PUnit.unit → False) → False) := by
  cases t with
  | base_1 g h => rfl

theorem index_eq_2 (t : T 0 false (fun g ↦ g PUnit.unit → False)) :
    (fun g ↦ g PUnit.unit → False) = (fun g : PUnit.{1} → Prop ↦ g PUnit.unit → False) := by
  cases t with
  | base_2 g h => rfl

def base_1_elim : T 0 true (fun g ↦ (g PUnit.unit → False) → False) → (g : PUnit.{1} → Prop) → ((g PUnit.unit → False) → False)
| T.base_1 g h => fun g' ↦ h

def base_2_elim : T 0 false (fun g ↦ g PUnit.unit → False) → (g : PUnit.{1} → Prop) → (g PUnit.unit → False)
| T.base_2 g h => fun g' ↦ h

theorem unsound_proof_of_false : False := by
  -- wait, how do we construct t_1 and t_2?
  -- We need g_sub1 and g_sub2.
  -- But wait, we still have the issue that g_sub1 and g_sub2 must be equal to apply them!
  -- But we can just choose the same g!
  -- Wait! If we choose the same g, say g = fun _ ↦ False.
  -- Then we cannot prove (g PUnit.unit → False) → False, which is (False → False) → False.
  -- Oh...
  sorry
