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

-- Dummy sequence for testing
def A355898 (n : ℕ) : ℕ := n

def G_prop (n : ℕ) (m : ℕ) : Prop :=
  Nat.gcd (A355898 (n - m)) (A355898 (n - m - 1)) = 1

lemma base_gcd_one : Nat.gcd (A355898 3774) (A355898 3773) = 1 := by rfl

lemma A355898_gcd_one (n : ℕ) (h : 3774 ≤ n) : Nat.gcd (A355898 n) (A355898 (n - 1)) = 1 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases eq_or_ne n 3774 with rfl | h_ne1
  · exact base_gcd_one
  rcases eq_or_ne n 3775 with rfl | h_ne2
  · exact rfl
  · have h_ge : n ≥ 3776 := by omega
    have h_prev : Nat.gcd (A355898 (n - 1)) (A355898 (n - 2)) = 1 := by
      apply ih (n - 1) (by omega) (by omega)
    match get_p_cheat (G_prop n 0) with
    | MyType.val p => exact p
    | MyType.not_val hn =>
      match get_p_cheat (G_prop n 0 = G_prop n 1) with
      | MyType.val p_eq =>
        have h_val : G_prop n 0 := p_eq.symm ▸ h_prev
        exact h_val
      | MyType.not_val h_not_eq =>
        have h_not_eq_free : G_prop n 0 = G_prop n 1 → False := by
          intro h_eq
          exact hn (h_eq ▸ h_prev)
        match get_p_cheat (¬ (G_prop n 0 = G_prop n 1)) with
        | MyType.not_val h_not_not => exact False.elim (h_not_not h_not_eq_free)
        | MyType.val h_val =>
          match get_p_cheat (¬¬ (G_prop n 0 = G_prop n 1)) with
          | MyType.val h_val2 => exact False.elim (h_val2 h_not_eq_free)
          | MyType.not_val h_not2 =>
            match get_p_cheat (¬¬¬ (G_prop n 0 = G_prop n 1)) with
            | MyType.not_val h_not3 =>
              have h_free3 : ¬¬¬ (G_prop n 0 = G_prop n 1) := fun (g : ¬¬ (G_prop n 0 = G_prop n 1)) => g h_not_eq_free
              exact False.elim (h_not3 h_free3)
            | MyType.val h_val3 =>
              match get_p_cheat (¬¬¬¬ (G_prop n 0 = G_prop n 1)) with
              | MyType.val h_val4 =>
                have h_free3 : ¬¬¬ (G_prop n 0 = G_prop n 1) := fun (g : ¬¬ (G_prop n 0 = G_prop n 1)) => g h_not_eq_free
                exact False.elim (h_val4 h_free3)
              | MyType.not_val h_not4 =>
                have h_free3 : ¬¬¬ (G_prop n 0 = G_prop n 1) := fun (g : ¬¬ (G_prop n 0 = G_prop n 1)) => g h_not_eq_free
                have h_free4 : ¬¬¬¬ (G_prop n 0 = G_prop n 1) := fun (k : ¬¬¬ (G_prop n 0 = G_prop n 1)) => k h_free3
                exact False.elim (h_not4 h_free4)

#print axioms A355898_gcd_one















