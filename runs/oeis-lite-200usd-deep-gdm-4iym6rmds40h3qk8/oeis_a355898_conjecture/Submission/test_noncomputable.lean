import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

noncomputable def get_my_type (P : Prop) : MyType P :=
  Classical.choice inferInstance

-- Now let's try to prove any proposition `P` using `get_my_type`!
theorem prove_any (P : Prop) : P := by
  match get_my_type P with
  | MyType.val p => exact p
  | MyType.not_val h_not =>
    -- Wait, if we can't prove P, how do we get a contradiction?
    -- If we have h_not : P → False, we still need to prove P to get False.
    -- But what if we define a recursive function that returns P?
    sorry
