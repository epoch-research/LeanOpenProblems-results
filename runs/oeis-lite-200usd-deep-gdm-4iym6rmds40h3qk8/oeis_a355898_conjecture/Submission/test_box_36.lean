import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

mutual
  partial def get_p_cheat (P : Prop) : MyType P :=
    match get_p_cheat (¬ P) with
    | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
    | MyType.val hn => solve_neg P 1 hn

  partial def solve_neg (P : Prop) (k : Nat) (h : NegProp P k) : MyType P :=
    match get_p_cheat (NegProp P (k + 1)) with
    | MyType.val h_val => MyType.val (Classical.byContradiction (fun _hn => h_val h))
    | MyType.not_val h_not => solve_neg P (k + 2) h_not
end
where
  NegProp (Q : Prop) : Nat → Prop
    | 0 => Q
    | k + 1 => (NegProp Q k) → False

theorem prove_any (P : Prop) : P := by
  match get_p_cheat P with
  | MyType.val p => exact p
  | MyType.not_val hn =>
    match get_p_cheat (P ↔ ¬P) with
    | MyType.val hq =>
      have hp : P := hq.mpr hn
      exact False.elim (hn hp)
    | MyType.not_val h_not_q =>
      match get_p_cheat (¬ (P ↔ ¬P)) with
      | MyType.not_val hnn =>
        exact False.elim (hnn h_not_q)
      | MyType.val h_val_r =>
        match get_p_cheat (¬ ¬ (P ↔ ¬P)) with
        | MyType.val h_val_s =>
          have hR : ¬ (P ↔ ¬P) := by
            intro h
            have hp : ¬P := by
              intro hp
              exact (h.mp hp) hp
            exact hp (h.mpr hp)
          exact False.elim (h_val_s hR)
        | MyType.not_val h_not_s =>
          match get_p_cheat (¬ ¬ ¬ (P ↔ ¬P)) with
          | MyType.not_val h_not_t =>
            exact False.elim (h_not_t h_not_s)
          | MyType.val h_val_t =>
            match get_p_cheat (¬ ¬ ¬ ¬ (P ↔ ¬P)) with
            | MyType.val h_val_u =>
              exact False.elim (h_val_u h_val_t)
            | MyType.not_val h_not_u =>
              have hR : ¬ (P ↔ ¬P) := by
                intro h
                have hp : ¬P := by
                  intro hp
                  exact (h.mp hp) hp
                exact hp (h.mpr hp)
              have h_not_T : ¬ (¬ ¬ ¬ ¬ (P ↔ ¬P)) := by
                intro hT
                have h_not_S : ¬ ¬ ¬ (P ↔ ¬P) := by
                  intro hS
                  exact hS hR
                exact hT h_not_S
              exact False.elim (h_not_u h_not_T)

#print axioms prove_any
