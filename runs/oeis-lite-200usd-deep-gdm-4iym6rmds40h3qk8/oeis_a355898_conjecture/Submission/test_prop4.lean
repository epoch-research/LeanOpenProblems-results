inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (MyType P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em (MyType P) with h | hnot
  · exact ⟨h⟩
  · -- hnot : MyType P → False
    exact ⟨MyType.not_val hnot⟩
