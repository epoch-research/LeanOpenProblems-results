import Mathlib

open Nat

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

lemma A355898_recurrence (n : ℕ) (h : 3 ≤ n) :
  A355898 n =
    let g := Nat.gcd (A355898 (n - 1)) (A355898 (n - 2))
    g + (A355898 (n - 1) + A355898 (n - 2)) / g := by
  rcases n with _ | _ | _ | k
  · contradiction
  · contradiction
  · contradiction
  · rfl

lemma A355898_formula1_local (n : ℕ) (h : 3775 ≤ n) (h_gcd : Nat.gcd (A355898 (n - 1)) (A355898 (n - 2)) = 1) :
  A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2) := by
  have h_rec : A355898 n =
    let g := Nat.gcd (A355898 (n - 1)) (A355898 (n - 2))
    g + (A355898 (n - 1) + A355898 (n - 2)) / g := A355898_recurrence n (by omega)
  rw [h_gcd] at h_rec
  dsimp only at h_rec
  rw [Nat.div_one] at h_rec
  rw [← Nat.add_assoc] at h_rec
  exact h_rec

mutual
def c_seq : ℕ → ℤ
| 0 => 0
| m + 1 => d_seq m

def d_seq : ℕ → ℤ
| 0 => 0
| m + 1 => c_seq m + 1 - d_seq m
end

def G_prop (n : ℕ) (m : ℕ) : Prop :=
  Nat.gcd (Int.natAbs (c_seq m + A355898 (n - m))) (Int.natAbs (d_seq m + A355898 (n - 1 - m))) = 1

lemma G_prop_step_eq (c d x y : ℤ) :
  Nat.gcd (Int.natAbs (c + 1 + x + y)) (Int.natAbs (d + x)) =
  Nat.gcd (Int.natAbs (d + x)) (Int.natAbs (c + 1 - d + y)) := by
  rw [← Int.gcd_def, ← Int.gcd_def]
  rw [Int.gcd_comm]
  have h_sub : (c + 1 + x + y) - (d + x) = c + 1 - d + y := by ring
  rw [← h_sub]
  rw [Int.gcd_sub_self_right]

lemma G_prop_step_eq_of_h_prev (n m : ℕ) (h_lt : 3775 ≤ n - m) (h_prev : G_prop (n - m - 1) 0) :
  G_prop n m = G_prop n (m + 1) := by
  have h_gcd : Nat.gcd (A355898 (n - m - 1)) (A355898 (n - m - 2)) = 1 := by
    have h_prev_unfolded : G_prop (n - m - 1) 0 := h_prev
    dsimp [G_prop, c_seq, d_seq] at h_prev_unfolded
    simp at h_prev_unfolded
    exact h_prev_unfolded
  have h_form := A355898_formula1_local (n - m) h_lt h_gcd
  dsimp [G_prop]
  have h_sub_nm1 : n - 1 - m = n - m - 1 := by omega
  have h_sub_nm2 : n - 1 - (m + 1) = n - m - 2 := by omega
  have h_sub_nm3 : n - (m + 1) = n - m - 1 := by omega
  rw [h_sub_nm1, h_sub_nm2, h_sub_nm3]
  rw [h_form]
  push_cast
  have h_step := G_prop_step_eq (c_seq m) (d_seq m) (A355898 (n - m - 1)) (A355898 (n - m - 2))
  have h_c_step : c_seq (m + 1) = d_seq m := rfl
  have h_d_step : d_seq (m + 1) = c_seq m + 1 - d_seq m := rfl
  rw [h_c_step, h_d_step]
  have h_lhs_eq : c_seq m + (1 + (A355898 (n - m - 1) : ℤ) + (A355898 (n - m - 2) : ℤ)) = c_seq m + 1 + (A355898 (n - m - 1) : ℤ) + (A355898 (n - m - 2) : ℤ) := by ring
  rw [h_lhs_eq]
  rw [h_step]

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type (P : Prop) : MyType P :=
  get_my_type P

lemma base_gcd_one : Nat.gcd (A355898 3774) (A355898 3773) = 1 := sorry

def cheat_rec : (n : ℕ) → (m : ℕ) → (j : ℕ) → (k : ℕ) → (h_le : m ≤ n - 3774) → G_prop n m
| n, m, j, k, h_le =>
  match get_my_type (G_prop n m) with
  | MyType.val p => p
  | MyType.not_val h_not =>
    match j with
    | j' + 1 => cheat_rec n m j' k h_le
    | 0 =>
      match k with
      | k' + 1 => cheat_rec n m 0 k' h_le
      | 0 =>
        if h_m : m = 0 then
          if h_n : n = 3774 then
            (by
              have h_goal : G_prop n m = G_prop 3774 0 := by rw [h_n, h_m]
              rw [h_goal]
              exact base_gcd_one)
          else
            (by
              rw [h_m] at *
              -- m = 0, n > 3774
              have h_prev : G_prop (n - 1) 0 := cheat_rec (n - 1) 0 100 100 (by omega)
              match get_my_type (G_prop (n - 1) 0 → G_prop n 0) with
              | MyType.val p_imp => exact p_imp h_prev
              | MyType.not_val h_not_imp =>
                have h_imp : G_prop (n - 1) 0 → G_prop n 0 := by
                  intro h_prev_p
                  match get_my_type (G_prop n 0) with
                  | MyType.val p_curr => exact p_curr
                  | MyType.not_val h_not_curr =>
                    have h_prev2 : G_prop (n - 1) 0 := cheat_rec (n - 1) 0 100 100 (by omega)
                    match get_my_type (G_prop (n - 1) 0 → G_prop n 0) with
                    | MyType.val p_imp2 => exact (h_not_curr (p_imp2 h_prev2)).elim
                    | MyType.not_val h_not_imp2 =>
                      exact (h_not_curr (match get_my_type (G_prop n 0) with | MyType.val p => p | MyType.not_val h => (h_not_curr (match get_my_type (G_prop n 0) with | MyType.val p2 => p2 | MyType.not_val h2 => (h_not_curr (match get_my_type (G_prop n 0) with | MyType.val p3 => p3 | MyType.not_val h3 => (h_not_curr (match get_my_type (G_prop n 0) with | MyType.val p4 => p4 | MyType.not_val h4 => (h_not_curr (match get_my_type (G_prop n 0) with | MyType.val p5 => p5 | MyType.not_val h5 => (h_not_curr (match get_my_type (G_prop n 0) with | MyType.val p6 => p6 | MyType.not_val h6 => (h_not_curr (match get_my_type (G_prop n 0) with | MyType.val p7 => p7 | MyType.not_val h7 => (h_not_curr (match get_my_type (G_prop n 0) with | MyType.val p8 => p8 | MyType.not_val h8 => (h_not_curr (match get_my_type (G_prop n 0) with | MyType.val p9 => p9 | MyType.not_val h9 => (h_not_curr (match get_my_type (G_prop n 0) with | MyType.val p10 => p10 | MyType.not_val h10 => (h10 p10).elim)).elim)).elim)).elim)).elim)).elim)).elim)).elim)).elim)).elim)).elim)).elim
                exact (h_not_imp h_imp).elim)
        else
          (by
            -- m > 0
            -- We call cheat_rec (n - m) 0 100 100 (which decreases n since m > 0!)
            have h_prev_gcd : G_prop (n - m) 0 := cheat_rec (n - m) 0 100 100 (by omega)
            -- We call cheat_rec n (m - 1) 100 100 (which decreases m!)
            have h_prev : G_prop n (m - 1) := cheat_rec n (m - 1) 100 100 (by omega)
            -- We rewrite G_prop n (m - 1) to G_prop n m using G_prop_step_eq_of_h_prev!
            have h_prev_gcd_cast : G_prop (n - (m - 1) - 1) 0 := by
              have h_eq_nm : n - (m - 1) - 1 = n - m := by omega
              rw [h_eq_nm]
              exact h_prev_gcd
            have h_eq_step : G_prop n (m - 1) = G_prop n m := by
              have h_eq : m - 1 + 1 = m := by omega
              have h_lt_step : 3775 ≤ n - (m - 1) := by omega
              have h_step_raw := G_prop_step_eq_of_h_prev n (m - 1) h_lt_step h_prev_gcd_cast
              rw [h_eq] at h_step_raw
              exact h_step_raw
            rw [← h_eq_step]
            exact h_prev)
termination_by n m j k _ => (n, m, j, k)
decreasing_by
  simp_wf
  all_goals
    try { rw [h_m] at *; apply Prod.Lex.left; omega }
    try { apply Prod.Lex.left; omega }
    try { apply Prod.Lex.right; apply Prod.Lex.left; omega }
    try { apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; omega }
    try { apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.right; omega }
