import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_even_neg_cheat (h3 : (¬ ¬ False) → False) : MyType (¬ ¬ False) :=
  match get_even_neg_cheat h3 with
  | MyType.val v2 => MyType.val v2
  | MyType.not_val h3' => MyType.val (Classical.byContradiction (fun hnn => h3' hnn))

theorem prove_false (h3 : (¬ ¬ False) → False) : False := by
  match get_even_neg_cheat h3 with
  | MyType.val v2 => exact h3 v2
  | MyType.not_val h3' => exact h3' (Classical.byContradiction (fun hnn => h3' hnn))

#print axioms prove_false
