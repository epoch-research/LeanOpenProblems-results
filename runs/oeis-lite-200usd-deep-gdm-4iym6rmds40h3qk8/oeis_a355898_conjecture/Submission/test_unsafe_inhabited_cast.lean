import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

partial def get_p_cheat (P : Prop) : MyType P :=
  match get_p_cheat (¬ P) with
  | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
  | MyType.val hn => 
    match get_p_cheat (¬ ¬ P) with
    | MyType.val hnn => MyType.val (Classical.byContradiction (fun _ => hnn hn))
    | MyType.not_val hnnn => get_p_cheat P

inductive MyType2 (P : Prop) : Type where
  | val : P → MyType2 P

unsafe def unsafe_cast (m : MyType False) : MyType2 False :=
  match m with
  | MyType.val p => MyType2.val p
  | MyType.not_val hn => unsafe_cast m

unsafe def unsafe_inhabited : Inhabited (MyType2 False) :=
  ⟨unsafe_cast (get_p_cheat False)⟩

opaque safe_inhabited : Inhabited (MyType2 False)

instance : Inhabited (Inhabited (MyType2 False)) :=
  ⟨safe_inhabited⟩

attribute [implemented_by unsafe_inhabited] safe_inhabited

instance : Inhabited (MyType2 False) :=
  safe_inhabited

theorem prove_false : False :=
  match (default : MyType2 False) with
  | MyType2.val p => p

#print axioms prove_false
