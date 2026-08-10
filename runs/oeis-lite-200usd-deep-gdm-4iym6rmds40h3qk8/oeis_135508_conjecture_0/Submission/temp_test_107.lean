import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

lemma x_seq_dvd_x_seq_succ (n : ℕ) (h : n > 0) : x_seq n ∣ x_seq (n + 1) := by
  cases n with
  | zero => contradiction
  | succ n =>
    cases n with
    | zero =>
      decide
    | succ n =>
      have : x_seq (n + 3) = 2 * x_seq (n + 2) + Nat.lcm (x_seq (n + 2)) (n + 3) := rfl
      rw [this]
      apply Nat.dvd_add
      · simp
      · apply Nat.dvd_lcm_left

lemma x_seq_dvd_x_seq_add (n k : ℕ) (hn : n > 0) : x_seq n ∣ x_seq (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_succ : x_seq (n + k) ∣ x_seq (n + k + 1) := x_seq_dvd_x_seq_succ (n + k) (by omega)
    exact Nat.dvd_trans ih h_succ

lemma x_seq_dvd_x_seq_of_le {n m : ℕ} (hn : n > 0) (h : n ≤ m) : x_seq n ∣ x_seq m := by
  have : m = n + (m - n) := by omega
  rw [this]
  exact x_seq_dvd_x_seq_add n (m - n) hn

def x_seq_loop : ℕ → ℕ → ℕ → ℕ
| 0, _, x => x
| n + 1, i, x => x_seq_loop n (i + 1) (2 * x + Nat.lcm x i)

def x_seq_tr (n : ℕ) : ℕ :=
  if n = 0 then 0
  else x_seq_loop (n - 1) 2 1

lemma x_seq_step (n : ℕ) (hn : n ≥ 1) :
    x_seq (n + 1) = 2 * x_seq n + Nat.lcm (x_seq n) (n + 1) := by
  cases n with
  | zero => contradiction
  | succ n => rfl

lemma x_seq_loop_eq (k n : ℕ) (hn : n ≥ 1) :
    x_seq_loop k (n + 1) (x_seq n) = x_seq (n + k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp [x_seq_loop]
    rw [← x_seq_step n hn]
    have ih' := ih (n + 1) (by omega)
    rw [ih']
    have : n + 1 + k = n + (k + 1) := by omega
    rw [this]

lemma x_seq_tr_eq (n : ℕ) : x_seq_tr n = x_seq n := by
  unfold x_seq_tr
  split_ifs with h
  · rw [h]; rfl
  · have hn : n ≥ 1 := by omega
    have h_loop := x_seq_loop_eq (n - 1) 1 (by decide)
    simp at h_loop
    have h_eq : x_seq_loop (n - 1) 2 1 = x_seq_loop (n - 1) 2 (x_seq 1) := rfl
    rw [h_eq]
    rw [h_loop]
    have : 1 + (n - 1) = n := by omega
    rw [this]

lemma test_107_full : 107 ∣ x_seq (107 * 107 - 1) := by
  have h_dvd : 107 ∣ x_seq_tr 2459 := by decide
  have h_eq : x_seq_tr 2459 = x_seq 2459 := x_seq_tr_eq 2459
  rw [h_eq] at h_dvd
  exact Nat.dvd_trans h_dvd (x_seq_dvd_x_seq_of_le (by decide) (by decide))
