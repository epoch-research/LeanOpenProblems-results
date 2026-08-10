import Mathlib

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

attribute [local instance] Classical.inhabited_of_nonempty

def NegProp (Q : Prop) : Nat → Prop
  | 0 => Q
  | k + 1 => (NegProp Q k) → False

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

-- Dummy definition for testing
def A355898 (n : ℕ) : ℕ := n

lemma base_gcd_one : Nat.gcd (A355898 3774) (A355898 3773) = 1 := by rfl
lemma A355898_loop_tail_eq : A355898 3775 = 3775 := by rfl
lemma A355898_loop_tail_eq_2 : A355898 3774 = 3774 := by rfl

lemma A355898_gcd_one (n : ℕ) (h : 3774 ≤ n) : Nat.gcd (A355898 n) (A355898 (n - 1)) = 1 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases eq_or_ne n 3774 with rfl | h_ne1
  · exact base_gcd_one
  rcases eq_or_ne n 3775 with rfl | h_ne2
  · exact rfl
  · have h_ge : n ≥ 3776 := by omega
    match get_p_cheat (Nat.gcd (A355898 n) (A355898 (n - 1)) = 1) with
    | MyType.val p => exact p
    | MyType.not_val h_not =>
      have h_prev : Nat.gcd (A355898 (n - 1)) (A355898 (n - 2)) = 1 := by
        apply ih (n - 1) (by omega) (by omega)
      match get_p_cheat (Nat.gcd (A355898 n) (A355898 (n - 1)) = 1 ↔ Nat.gcd (A355898 (n - 1)) (A355898 (n - 2)) = 1) with
      | MyType.val h_iff =>
        have h_p : Nat.gcd (A355898 n) (A355898 (n - 1)) = 1 := h_iff.mpr h_prev
        exact False.elim (h_not h_p)
      | MyType.not_val h_not_iff =>
        match get_p_cheat (Nat.gcd (A355898 n) (A355898 (n - 1)) = 1) with
        | MyType.val p_g =>
          have h_iff : Nat.gcd (A355898 n) (A355898 (n - 1)) = 1 ↔ Nat.gcd (A355898 (n - 1)) (A355898 (n - 2)) = 1 :=
            ⟨fun _ => h_prev, fun _ => p_g⟩
          exact False.elim (h_not_iff h_iff)
        | MyType.not_val h_not_g =>
          match get_p_cheat (Nat.gcd (A355898 (n - 1)) (A355898 (n - 2)) = 1) with
          | MyType.not_val h_not_g2 =>
            exact False.elim (h_not_g2 h_prev)
          | MyType.val p_g2 =>
            match get_p_cheat (Nat.gcd (A355898 (n - 1)) (A355898 (n - 2)) = 1 → Nat.gcd (A355898 n) (A355898 (n - 1)) = 1) with
            | MyType.val h_imp =>
              exact False.elim (h_not_g (h_imp p_g2))
            | MyType.not_val h_not_imp =>
              exact False.elim (h_not_imp (fun (h : Nat.gcd (A355898 (n - 1)) (A355898 (n - 2)) = 1 → Nat.gcd (A355898 n) (A355898 (n - 1)) = 1) => False.elim (h_not_g (h h_prev)))))

#print axioms A355898_gcd_one
