import Mathlib

def P_Q : ℕ → ℤ × ℤ
| 0 => (0, 1)
| (n + 1) => 
  let ⟨p, q⟩ := P_Q n
  (q + p, q + 2*p)

def P (n : ℕ) : ℤ := (P_Q n).1
def Q (n : ℕ) : ℤ := (P_Q n).2

lemma PQ_step (n : ℕ) : P (n + 1) = Q n + P n ∧ Q (n + 1) = Q n + 2 * P n := by
  unfold P Q
  have h : P_Q (n + 1) = (Q n + P n, Q n + 2 * P n) := by
    unfold P_Q
    rcases h_eq : P_Q n with ⟨p, q⟩
    unfold P Q
    rw [h_eq]
  rw [h]
  exact ⟨rfl, rfl⟩

lemma PQ_rel (n : ℕ) : (Q n)^2 - 2 * (P n)^2 = (-1 : ℤ)^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hP := (PQ_step n).1
    have hQ := (PQ_step n).2
    rw [hP, hQ]
    calc (Q n + 2 * P n)^2 - 2 * (Q n + P n)^2
      _ = (Q n)^2 + 4 * Q n * P n + 4 * (P n)^2 - 2 * ((Q n)^2 + 2 * Q n * P n + (P n)^2) := by ring
      _ = -((Q n)^2 - 2 * (P n)^2) := by ring
      _ = -((-1 : ℤ)^n) := by rw [ih]
      _ = (-1 : ℤ)^(n + 1) := by ring

lemma PQ_pos (n : ℕ) : 0 ≤ P n ∧ 0 < Q n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hP := (PQ_step n).1
    have hQ := (PQ_step n).2
    rw [hP, hQ]
    constructor
    · linarith
    · linarith

lemma P_strict_pos (n : ℕ) (hn : 0 < n) : 0 < P n := by
  cases n with
  | zero => contradiction
  | succ n =>
    have hP := (PQ_step n).1
    have h1 := (PQ_pos n).1
    have h2 := (PQ_pos n).2
    linarith

lemma PQ_rel_odd (j : ℕ) (hj : 0 < j) : (Q (2*j - 1))^2 = 2 * (P (2*j - 1))^2 - 1 := by
  have h := PQ_rel (2*j - 1)
  have h_odd : (-1 : ℤ)^(2*j - 1) = -1 := by
    have h_pow : (-1 : ℤ)^(2*j - 1) = (-1 : ℤ)^(2*(j-1) + 1) := by
      congr 1
      omega
    rw [h_pow, pow_add, pow_mul]
    norm_num
  rw [h_odd] at h
  linarith

lemma PQ_rel_even (j : ℕ) : (Q (2*j))^2 = 2 * (P (2*j))^2 + 1 := by
  have h := PQ_rel (2*j)
  have h_even : (-1 : ℤ)^(2*j) = 1 := by
    rw [pow_mul]
    norm_num
  rw [h_even] at h
  linarith
