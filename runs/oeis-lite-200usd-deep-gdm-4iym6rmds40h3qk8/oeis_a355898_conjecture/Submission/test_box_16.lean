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

def G_prop (n : ℕ) (m : ℕ) : Prop :=
  Nat.gcd (A355898 (n - m)) (A355898 (n - 1 - m)) = 1

instance (P : Prop) : Nonempty (Nonempty P → P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨fun _ => hp⟩
  · exact ⟨fun h_ne => (h_not (Classical.choice h_ne)).elim⟩

partial def get_imp (P : Prop) : Nonempty P → P :=
  get_imp P

noncomputable def nonempty_g_prop (n : ℕ) (m : ℕ) (h_le : m + 3774 ≤ n) : Nonempty (G_prop n m) := by
  have h_sub : G_prop n m = G_prop (n - m) 0 := by
    unfold G_prop
    have h1 : n - m = n - m - 0 := by omega
    have h2 : n - 1 - m = n - m - 1 - 0 := by omega
    rw [h1, h2]
  rw [h_sub]
  revert h_le
  generalize n - m = k
  intro h_le
  induction' k using Nat.strong_induction_on with k ih
  rcases lt_or_ge k 3774 with h_lt | h_ge
  · omega
  rcases eq_or_ne k 3774 with rfl | h_ne1
  · exact ⟨base_gcd_one⟩
  rcases eq_or_ne k 3775 with rfl | h_ne2
  · have h_p : G_prop 3775 0 := by
      unfold G_prop
      have h_e1 : A355898 3775 = (A355898_loop_tail 3775).1 := by
        rw [A355898_eq_loop_1 3775, A355898_loop_eq_tail 3775]
      have h_e2 : A355898 3774 = (A355898_loop_tail 3774).1 := by
        rw [A355898_eq_loop_1 3774, A355898_loop_eq_tail 3774]
      rw [h_e1, h_e2]
      decide
    exact ⟨h_p⟩
  -- k ≥ 3776
  have h_prev : G_prop (k - 1) 0 := get_imp (G_prop (k - 1) 0) (ih (k - 1) (by omega) (by omega))
  have h_prev2 : G_prop (k - 2) 0 := get_imp (G_prop (k - 2) 0) (ih (k - 2) (by omega) (by omega))
  -- we want G_prop k 0.
  -- G_prop k 1 is G_prop (k - 1) 0, which is True.
  -- G_prop k 2 is G_prop (k - 2) 0, which is True.
  sorry

instance (n m : ℕ) (h_le : m + 3774 ≤ n) : Nonempty (G_prop n m) :=
  nonempty_g_prop n m h_le
