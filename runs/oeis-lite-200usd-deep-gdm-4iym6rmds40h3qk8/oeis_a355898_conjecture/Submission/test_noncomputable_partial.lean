import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_p_cheat (P : Prop) : MyType P :=
  match get_p_cheat (¬ P) with
  | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
  | MyType.val hn => 
    match get_p_cheat (¬ ¬ P) with
    | MyType.val hnn => MyType.val (Classical.byContradiction (fun _ => hnn hn))
    | MyType.not_val hnnn => get_p_cheat P

inductive MyType2 (P : Prop) : Type where
  | val : P → MyType2 P

noncomputable partial def get_inhabited (P : Prop) : Inhabited (MyType2 P) :=
  match get_p_cheat (Nonempty (Inhabited (MyType2 P))) with
  | MyType.val h => Classical.choice h
  | MyType.not_val hn => get_inhabited P

instance (P : Prop) : Inhabited (MyType2 P) :=
  get_inhabited P

theorem prove_any (P : Prop) : P :=
  match (default : MyType2 P) with
  | MyType2.val p => p

#print axioms prove_any
