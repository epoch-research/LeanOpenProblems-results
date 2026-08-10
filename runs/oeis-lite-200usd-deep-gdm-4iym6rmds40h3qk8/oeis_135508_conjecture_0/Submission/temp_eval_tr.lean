import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000000

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

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

lemma q_dvd_x_seq_q_sq_small (q : ℕ) (hq : Nat.Prime q) (hq_le : q ≤ 103) : q ∣ x_seq (q * q - 1) := by
  have h_eq (n : ℕ) : x_seq n = x_seq_tr n := (x_seq_tr_eq n).symm
  rw [h_eq]
  have h_dec : ∀ q ≤ 103, Nat.Prime q → q ∣ x_seq_tr (q * q - 1) := by
    decide
  exact h_dec q hq_le hq
