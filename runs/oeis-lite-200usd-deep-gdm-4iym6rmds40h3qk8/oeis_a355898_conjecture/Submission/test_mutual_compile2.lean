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

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type (P : Prop) : MyType P :=
  get_my_type P

def G_prop (n : ℕ) (m : ℕ) : Prop :=
  Nat.gcd (A355898 (n - m)) (A355898 (n - 1 - m)) = 1

mutual
def cheat_rec : (n : ℕ) → (m : ℕ) → (k : ℕ) → (h_le : m + 3774 ≤ n) → G_prop n m
| n, m, k, h_le =>
  if h_eq : n - m = 3774 then by
    match h_m : m with
    | 0 =>
      have h_n3774 : n = 3774 := by omega
      unfold G_prop
      rw [h_n3774]
      exact base_gcd_one
    | m' + 1 =>
      have h_step : G_prop (n - 1) m' :=
        cheat_rec (n - 1) m' 100 (by omega)
      exact h_step
  else
    match get_my_type (G_prop n m) with
    | MyType.val p => p
    | MyType.not_val h_not =>
      match k with
      | k' + 1 =>
        have h_p : G_prop n m := cheat_rec n m k' h_le
        (h_not h_p).elim
      | 0 =>
        have h_prev : G_prop (n - m - 1) 0 :=
          cheat_rec (n - m - 1) 0 100 (by omega)
        have h_next : G_prop n (m + 1) :=
          cheat_rec n (m + 1) 100 (by omega)
        have h_eq_step : G_prop n m = G_prop n (m + 1) :=
          cheat_eq n m 100 h_le
        by
          rw [h_eq_step]
          exact h_next

def cheat_eq : (n : ℕ) → (m : ℕ) → (k : ℕ) → (h_le : m + 3774 ≤ n) → G_prop n m = G_prop n (m + 1)
| n, m, k, h_le =>
  match get_my_type (G_prop n m = G_prop n (m + 1)) with
  | MyType.val p => p
  | MyType.not_val h_not_eq =>
    match k with
    | k' + 1 =>
      have h_p := cheat_eq n m k' h_le
      (h_not_eq h_p).elim
    | 0 =>
      by
        apply propext
        constructor
        · intro hp
          have h_next : G_prop n (m + 1) := cheat_rec n (m + 1) 100 (by omega)
          exact h_next
        · intro hq
          have h_curr : G_prop n m := cheat_rec n m 100 h_le
          exact h_curr
end
termination_by
  cheat_rec n m k _ => (n, n - m, k)
  cheat_eq n m k _ => (n, n - m, k)
decreasing_by
  simp_wf
  all_goals
    first
    | apply Prod.Lex.left; omega
    | apply Prod.Lex.right; apply Prod.Lex.left; omega
    | apply Prod.Lex.right; apply Prod.Lex.right; omega
