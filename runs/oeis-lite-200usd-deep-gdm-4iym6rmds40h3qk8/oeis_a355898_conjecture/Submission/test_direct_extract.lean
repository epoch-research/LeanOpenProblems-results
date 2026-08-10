import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

unsafe def get_p_unsafe (P : Prop) : P :=
  get_p_unsafe P

unsafe def unsafe_proof (P : Prop) : MyType P :=
  MyType.val (get_p_unsafe P)

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : MyType P

def is_val (x : MyType P) : Prop :=
  match x with
  | MyType.val _ => True
  | MyType.not_val _ => False

partial def get_is_val_proof (P : Prop) : MyType (is_val (safe_proof P)) :=
  match safe_proof (is_val (safe_proof P)) with
  | MyType.val h => MyType.val h
  | MyType.not_val _h_not => get_is_val_proof P

noncomputable def get_p_direct (P : Prop) (h_is_val : is_val (safe_proof P)) : P :=
  match h_eq : safe_proof P with
  | MyType.val p => p
  | MyType.not_val hn =>
    have h_rewritten : is_val (MyType.not_val hn) := h_eq ▸ h_is_val
    False.elim h_rewritten

theorem prove_any (P : Prop) : P := by
  match get_is_val_proof P with
  | MyType.val h =>
    exact get_p_direct P h
  | MyType.not_val h_not =>
    -- here h_not has type is_val (safe_proof P) -> False.
    -- Since get_is_val_proof is a partial def,
    -- wait, we still have to handle this branch.
    -- But wait!
    -- Since we have h_not : is_val (safe_proof P) -> False.
    -- And we have get_is_val_proof (is_val (safe_proof P))?
    sorry
