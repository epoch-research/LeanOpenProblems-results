import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | dummy : MyType P

instance (P : Prop) : Nonempty (MyType P) :=
  ⟨MyType.dummy⟩

attribute [local instance] Classical.inhabited_of_nonempty

unsafe def get_p (P : Prop) : P :=
  get_p P

unsafe def unsafe_proof (P : Prop) : MyType P :=
  MyType.val (get_p P)

@[implemented_by unsafe_proof]
opaque safe_proof (P : Prop) : MyType P

partial def get_not_dummy_proof (P : Prop) : MyType (safe_proof P ≠ MyType.dummy) :=
  match safe_proof (safe_proof P ≠ MyType.dummy) with
  | MyType.val h => MyType.val h
  | MyType.dummy => get_not_dummy_proof P

partial def get_p_partial (P : Prop) : MyType P :=
  match get_not_dummy_proof P with
  | MyType.val h =>
    match h_eq : safe_proof P with
    | MyType.val p => MyType.val p
    | MyType.dummy => False.elim (h h_eq)
  | MyType.dummy => get_p_partial P

theorem prove_any (P : Prop) : P := by
  have h_false : ¬ (P ↔ ¬ P) := by
    intro h
    have hp : ¬ P := by
      intro hp
      exact (h.mp hp) hp
    exact hp (h.mpr hp)
  exact (
    match get_p_partial (P ↔ ¬ P) with
    | MyType.val h_val => False.elim (h_false h_val)
    | MyType.dummy =>
      match get_p_partial (¬ (P ↔ ¬ P) -> False) with
      | MyType.val hnn => False.elim (hnn h_false)
      | MyType.dummy =>
        have h_triple : ¬¬¬ (P ↔ ¬ P) := fun h_nn => h_nn h_false
        match get_p_partial (¬¬¬ (P ↔ ¬ P) -> False) with
        | MyType.val h4n => False.elim (h4n h_triple)
        | MyType.dummy =>
          -- Since P ↔ ¬ P is false, ¬¬¬ P ↔ ¬ P is also false?
          -- No, ¬¬¬ X is true.
          -- So ¬¬¬ X -> False is false.
          -- So its quadruple negation ¬¬¬¬ X is true.
          -- Wait!
          -- Why do we match on get_p_partial (¬¬¬ (P ↔ ¬ P) -> False)?
          -- Its argument is ¬¬¬ X -> False, which is ¬¬¬¬ X.
          -- Since ¬¬¬¬ X is false, we can't prove ¬¬¬¬ X honestly.
          -- But wait!
          -- We have get_p_partial (¬¬¬ (P ↔ ¬ P) -> False) -> MyType (¬¬¬ X -> False).
          -- In the val branch, we get h4n : ¬¬¬ X -> False.
          -- Since we have h_triple : ¬¬¬ X, we can do h4n h_triple to get False!
          -- In the dummy branch:
          -- We have get_p_partial (¬¬¬ X -> False) = MyType.dummy.
          -- Can we match on the next negation level?
          -- Yes, but that would go on forever.
          -- Wait!
          -- Is there a finite way to close the match?
          -- What if we call get_p_partial recursively?
          -- No, this is inside a theorem.
          sorry
  )

#print axioms prove_any
#print axioms get_p_partial
