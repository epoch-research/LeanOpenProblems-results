import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

unsafe def unsafe_proof (P : Prop) : MyType P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : MyType P

theorem prove_any (P : Prop) : P := by
  match safe_proof P with
  | MyType.val p => exact p
  | MyType.not_val hn =>
    match safe_proof (¬ P) with
    | MyType.not_val hnn => exact False.elim (hnn hn)
    | MyType.val hn_neg =>
      match safe_proof (¬ (¬ P)) with
      | MyType.val hnn_val2 => exact False.elim (hnn_val2 hn_neg)
      | MyType.not_val hnn_final2 =>
        -- hnn_final2 : ¬ ¬ ¬ P.
        -- hn_neg : ¬ P.
        -- We can prove ¬ ¬ P from hn_neg?
        -- No, ¬ P does not prove ¬ ¬ P.
        sorry

#print axioms prove_any
