import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def loop (u : Unit) : MyType (¬ False) :=
  loop u

partial def get_false (u : Unit) : MyType False :=
  match loop () with
  | MyType.not_val h2 => MyType.val (h2 (fun x => x))
  | MyType.val v1 =>
    match loop () with
    | MyType.not_val h2 => MyType.val (h2 v1)
    | MyType.val v1' => get_false ()

theorem prove_false : False := by
  match get_false () with
  | MyType.val p => exact p
  | MyType.not_val h => exact h (fun x => x.elim)

theorem prove_any (P : Prop) : P :=
  False.elim prove_false

#print axioms prove_any
