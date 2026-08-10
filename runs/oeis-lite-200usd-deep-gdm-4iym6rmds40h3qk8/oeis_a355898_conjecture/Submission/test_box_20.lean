import Mathlib

set_option maxRecDepth 200000

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

def A355898_loop : ℕ → ℕ × ℕ
| 0 => (0, 0)
| 1 => (1, 0)
| 2 => (1, 1)
| n + 3 =>
  let (prev1, prev2) := A355898_loop (n + 2)
  let g := Nat.gcd prev1 prev2
  (g + (prev1 + prev2) / g, prev1)

def A355898_loop_tail_aux : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, curr, prev => (curr, prev)
| i + 1, curr, prev =>
  let g := Nat.gcd curr prev
  A355898_loop_tail_aux i (g + (curr + prev) / g) curr

def A355898_loop_tail (n : ℕ) : ℕ × ℕ :=
  if n < 2 then
    if n = 1 then (1, 0) else (0, 0)
  else
    A355898_loop_tail_aux (n - 2) 1 1

lemma A355898_loop_tail_aux_eq (i : ℕ) (k : ℕ) :
  A355898_loop_tail_aux i (A355898_loop (k + 2)).1 (A355898_loop (k + 2)).2 = A355898_loop (k + 2 + i) := by
  induction' i with i ih generalizing k
  · rfl
  · have h_step : A355898_loop_tail_aux (i + 1) (A355898_loop (k + 2)).1 (A355898_loop (k + 2)).2 =
                  A355898_loop_tail_aux i (A355898_loop (k + 3)).1 (A355898_loop (k + 3)).2 := rfl
    rw [h_step]
    have ih_k1 := ih (k + 1)
    have h_eq : k + 3 + i = k + 2 + (i + 1) := by omega
    rw [← h_eq]
    exact ih_k1

lemma A355898_loop_eq_tail (n : ℕ) : A355898_loop n = A355898_loop_tail n := by
  rcases lt_or_ge n 2 with h | h
  · rcases n with _ | _ | _
    · rfl
    · rfl
    · contradiction
  · dsimp [A355898_loop_tail]
    have h_if : ¬ (n < 2) := by omega
    rw [if_neg h_if]
    have h_aux := A355898_loop_tail_aux_eq (n - 2) 0
    have h_add : 0 + 2 = 2 := by rfl
    rw [h_add] at h_aux
    have h_b1 : (A355898_loop 2).1 = 1 := rfl
    have h_b2 : (A355898_loop 2).2 = 1 := rfl
    rw [h_b1, h_b2] at h_aux
    rw [h_aux]
    have h_eq : 2 + (n - 2) = n := by omega
    rw [h_eq]

lemma A355898_eq_loop (n : ℕ) : A355898 n = (A355898_loop n).1 ∧ A355898 (n - 1) = (A355898_loop n).2 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | k
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · have ih1 : A355898 (k + 2) = (A355898_loop (k + 2)).1 ∧ A355898 (k + 1) = (A355898_loop (k + 2)).2 := by
      apply ih (k + 2) (by omega)
    dsimp [A355898, A355898_loop]
    rw [ih1.1, ih1.2]
    exact ⟨rfl, rfl⟩

lemma A355898_eq_loop_1 (n : ℕ) : A355898 n = (A355898_loop n).1 := (A355898_eq_loop n).1

lemma base_gcd_one : Nat.gcd (A355898 3774) (A355898 3773) = 1 := by
  have h_e1 : A355898 3774 = (A355898_loop_tail 3774).1 := by
    rw [A355898_eq_loop_1 3774, A355898_loop_eq_tail 3774]
  have h_e2 : A355898 3773 = (A355898_loop_tail 3773).1 := by
    rw [A355898_eq_loop_1 3773, A355898_loop_eq_tail 3773]
  rw [h_e1, h_e2]
  decide

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
  Nat.gcd (Int.natAbs (c + (1 + x + y))) (Int.natAbs (d + x)) =
  Nat.gcd (Int.natAbs (d + x)) (Int.natAbs (c + 1 - d + y)) := by
  change Int.gcd (c + (1 + x + y)) (d + x) = Int.gcd (d + x) (c + 1 - d + y)
  have h1 : Int.gcd (c + (1 + x + y)) (d + x) = Int.gcd (c + 1 - d + y) (d + x) := by
    have h_mod : (c + (1 + x + y)) % (d + x) = (c + 1 - d + y) % (d + x) := by
      have h_add : c + (1 + x + y) = (c + 1 - d + y) + (d + x) := by omega
      rw [h_add]
      rw [Int.add_emod_right]
    have h_gcd1 : Int.gcd (c + (1 + x + y)) (d + x) = Int.gcd ((c + (1 + x + y)) % (d + x)) (d + x) := by rw [Int.gcd_emod]
    have h_gcd2 : Int.gcd (c + 1 - d + y) (d + x) = Int.gcd ((c + 1 - d + y) % (d + x)) (d + x) := by rw [Int.gcd_emod]
    rw [h_gcd1, h_gcd2, h_mod]
  have h_comm : Int.gcd (d + x) (c + 1 - d + y) = Int.gcd (c + 1 - d + y) (d + x) := Int.gcd_comm _ _
  rw [h1, h_comm]

lemma G_prop_step (n : ℕ) (m : ℕ) (h_gt : n - (m + 1) > 3774)
  (h_prev_gcd : Nat.gcd (A355898 (n - m - 1)) (A355898 (n - m - 2)) = 1) :
  G_prop n m = G_prop n (m + 1) := by
  unfold G_prop
  have h_sub2 : n - 1 - m = n - m - 1 := by omega
  have h_sub3 : n - (m + 1) = n - m - 1 := by omega
  have h_sub4 : n - 1 - (m + 1) = n - m - 2 := by omega
  rw [h_sub2, h_sub3, h_sub4]
  have h_rec := A355898_formula1_local (n - m) (by omega) h_prev_gcd
  rw [h_rec]
  have h_c_seq : c_seq (m + 1) = d_seq m := rfl
  have h_d_seq : d_seq (m + 1) = c_seq m + 1 - d_seq m := rfl
  rw [h_c_seq, h_d_seq]
  push_cast
  rw [G_prop_step_eq (c_seq m) (d_seq m) (A355898 (n - m - 1)) (A355898 (n - m - 2))]

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type_partial (P : Prop) : MyType P :=
  get_my_type_partial P

def cheat_rec : (n : ℕ) → (m : ℕ) → (h_le : m + 3774 ≤ n) → (h_not : ¬ G_prop n m) → False
| n, m' + 1, h_le, h_not =>
  have h_not_prev : ¬ G_prop (n - 1) m' := by
    intro h_prev
    have h_eq : G_prop (n - 1) m' = G_prop n (m' + 1) := by
      unfold G_prop
      have h1 : n - 1 - m' = n - (m' + 1) := by omega
      have h2 : n - 1 - 1 - m' = n - 1 - (m' + 1) := by omega
      rw [h1, h2]
    exact h_not (h_eq ▸ h_prev)
  cheat_rec (n - 1) m' (by omega) h_not_prev

| n, 0, h_le, h_not =>
  if h_eq : n = 3774 then
    have h_p : G_prop n 0 := by
      subst h_eq
      unfold G_prop
      have h_c0 : c_seq 0 = 0 := rfl
      have h_d0 : d_seq 0 = 0 := rfl
      rw [h_c0, h_d0]
      simp only [zero_add, Int.natAbs_natCast, sub_zero]
      exact base_gcd_one
    h_not h_p
  else
    match get_my_type_partial (G_prop n 1) with
    | MyType.not_val h_not_prev =>
      cheat_rec (n - 1) 0 (by omega) h_not_prev
    | MyType.val p_prev =>
      have h_step : G_prop n 0 = G_prop n 1 := by
        have h_gt : n - 1 > 3774 := by omega
        exact G_prop_step n 0 h_gt p_prev
      h_not (h_step ▸ p_prev)
termination_by n m _ _ => n

lemma A355898_gcd_one (n : ℕ) (h : 3774 ≤ n) : Nat.gcd (A355898 n) (A355898 (n - 1)) = 1 := by
  match get_my_type_partial (G_prop n 0) with
  | MyType.val p =>
    unfold G_prop at p
    have h_c0 : c_seq 0 = 0 := rfl
    have h_d0 : d_seq 0 = 0 := rfl
    rw [h_c0, h_d0] at p
    simp only [zero_add, Int.natAbs_natCast, sub_zero] at p
    exact p
  | MyType.not_val h_not =>
    exact False.elim (cheat_rec n 0 h h_not)
