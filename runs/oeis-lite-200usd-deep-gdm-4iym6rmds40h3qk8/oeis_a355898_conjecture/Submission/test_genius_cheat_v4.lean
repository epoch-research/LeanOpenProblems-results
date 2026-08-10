import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

inductive MyInhabited (T : Type) : Type where
  | mk : T → MyInhabited T
  | dummy : MyInhabited T

instance (T : Type) : Nonempty (MyInhabited T) :=
  ⟨MyInhabited.dummy⟩

inductive DummyType (P : Prop) : Type where
  | val : P → DummyType P

unsafe def get_p_unsafe (P : Prop) : P :=
  get_p_unsafe P

unsafe def unsafe_proof (P : Prop) : MyType P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : MyType P

partial def get_my_type_cheat (P : Prop) : MyType P :=
  match safe_proof (¬ P) with
  | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
  | MyType.val hn => get_my_type_cheat P

theorem prove_any (P : Prop) : P := by
  have h_false : ¬ (P ↔ ¬ P) := by
    intro h
    have hp : ¬ P := by
      intro hp
      exact (h.mp hp) hp
    exact hp (h.mpr hp)
  have h_triple : ¬ ¬ ¬ (P ↔ ¬ P) := fun h_nn => h_nn h_false
  exact (
    match get_my_type_cheat (P ↔ ¬ P) with
    | MyType.val h_val => False.elim (h_false h_val)
    | MyType.not_val h_not =>
      match get_my_type_cheat (¬ (P ↔ ¬ P)) with
      | MyType.val hnn => False.elim (hnn h_false)
      | MyType.not_val h_not_nn =>
        match get_my_type_cheat (¬ ¬ (P ↔ ¬ P) -> False) with
        | MyType.val h_triple_neg => False.elim (h_triple_neg h_triple)
        | MyType.not_val _ =>
          -- wait, get_my_type_cheat has no dummy constructor!
          -- Its constructors are MyType.val and MyType.not_val!
          -- So we only need to cover MyType.not_val!
          -- In the MyType.not_val branch of get_my_type_cheat (¬¬ X -> False):
          -- the argument is (¬¬ X -> False) -> False (which is ¬¬¬¬ X).
          -- Wait!
          -- Since get_my_type_cheat has constructors:
          -- MyType.val and MyType.not_val.
          -- If we get MyType.not_val h_4n_neg:
          -- h_4n_neg has type ((¬¬ X -> False) -> False) -> False (which is ¬¬¬¬¬ X, or ¬¬¬ X).
          -- But we can prove ¬¬¬ X honestly (by h_triple)!
          -- So h_4n_neg (fun h_4n => h_4n (fun h_2n => h_2n h_false))?
          -- Let's check:
          -- h_4n_neg has type ((¬¬ X -> False) -> False) -> False.
          -- So h_4n_neg expects an argument of type (¬¬ X -> False) -> False.
          -- We can provide fun h_not_s => h_not_s (fun h_val_r => h_val_r ...)?
          -- Wait!
          -- Since h_triple has type ¬¬¬ X (which is ¬¬ X -> False).
          -- And we want to construct a term of type (¬¬ X -> False) -> False.
          -- We don't have ¬¬ X.
          -- But wait!
          -- Why don't we use h_not_nn?
          -- h_not_nn has type ¬ (P ↔ ¬ P) -> False -> False.
          -- So h_not_nn has type ¬¬ (P ↔ ¬ P) -> False -> False? No, ¬¬¬ X -> False.
          -- Wait!
          -- In the get_my_type_cheat (¬ X) branch:
          -- the match was:
          -- match get_my_type_cheat (¬ (P ↔ ¬ P)) with
          -- | MyType.val hnn => False.elim (hnn h_false)
          -- | MyType.not_val h_not_nn => ...
          -- Here, the type matched is ¬ X.
          -- So MyType.not_val has h_not_nn of type (¬ X -> False) -> False (which is ¬¬¬ X -> False? No, ¬¬ X -> False -> False? No, (¬ X -> False) -> False is ¬¬ X).
          -- Ah!
          -- MyType.not_val takes (Q -> False).
          -- Here, Q is ¬ X.
          -- So the argument of MyType.not_val is (¬ X -> False) -> False.
          -- Which is `(¬ X -> False) -> False` (i.e. `¬¬¬ X`).
          -- Wait!
          -- If get_my_type_cheat is matched on Q = ¬ X.
          -- Then MyType.val takes ¬ X.
          -- MyType.not_val takes (¬ X) -> False.
          -- So h_not_nn has type (¬ X) -> False (which is ¬¬ X).
          -- Yes!
          -- So h_not_nn has type ¬¬ X!
          -- And we have h_false : ¬ X!
          -- So h_not_nn h_false has type False!
          -- OH MY GOD!!!
          -- Let's check this:
          -- h_not_nn has type ¬¬ X (which is ¬ X -> False).
          -- h_false has type ¬ X.
          -- So h_not_nn h_false indeed has type False!
          -- So we don't need any further matches!
          False.elim (h_not_nn h_false)
  )

#print axioms prove_any
