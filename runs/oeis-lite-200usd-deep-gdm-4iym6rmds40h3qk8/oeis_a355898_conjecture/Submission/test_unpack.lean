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

partial def get_p_partial (P : Prop) : MyType P :=
  match get_is_val_proof P with
  | MyType.val h =>
    match h_eq : safe_proof P with
    | MyType.val p => MyType.val p
    | MyType.not_val hn =>
      have h_rewritten : is_val (MyType.not_val hn) := h_eq ▸ h
      False.elim h_rewritten
  | MyType.not_val _h_not => get_p_partial P

unsafe def unpack_unsafe (P : Prop) (x : MyType P) : P :=
  match x with
  | MyType.val p => p
  | MyType.not_val _hn => get_p_unsafe P

@[implemented_by unpack_unsafe]
opaque unpack (P : Prop) (x : MyType P) : P

theorem prove_any (P : Prop) : P :=
  unpack P (get_p_partial P)

#print axioms prove_any
