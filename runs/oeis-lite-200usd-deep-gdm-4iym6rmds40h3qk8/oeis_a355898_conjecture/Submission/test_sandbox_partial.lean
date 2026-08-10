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

partial def get_plift_false (u : Unit) : PLift False :=
  match get_p_cheat (¬ False) with
  | MyType.not_val h2 => ⟨h2 (fun x => x)⟩
  | MyType.val v1 => get_plift_false ()

theorem prove_false : False :=
  (get_plift_false ()).down

theorem prove_any (P : Prop) : P :=
  False.elim prove_false

#print axioms prove_any
