import FormalConjectures.Util.ProblemImports

open Nat

/-- Helper function for the recurrence relation, defined over $\mathbb{Q}$. -/
noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 => -- Index $n = k+2$, $n \ge 2$
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    -- The subtraction n_idx - 1 is safe since n_idx ≥ 2
    let a_prev : ℚ := a_Q (n_idx - 1)

    -- Numerator Term 1: $32n^3 a(n-1)$
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev

    -- Polynomial coefficient Term 2
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1

    -- Binomial Term 2: $\binom{2n-1}{n}^4$. Subtraction is safe since $2n-1 \ge 3$
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4

    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3

    numerator / denominator

noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat

lemma val1 : a 1 = 2 := by rfl
lemma val2 : a 2 = 181 := by
  unfold a; rw [a_Q, a_Q]; norm_num; rfl

lemma val3 : a 3 = 23488 := by
  unfold a; rw [a_Q, a_Q, a_Q]
  simp [Nat.choose]
  norm_num
  rfl

lemma val4 : a 4 = 3625081 := by
  unfold a; rw [a_Q, a_Q, a_Q, a_Q]
  simp [Nat.choose]
  norm_num
  rfl

lemma val5 : a 5 = 619898336 := by
  unfold a; rw [a_Q, a_Q, a_Q, a_Q, a_Q]
  simp [Nat.choose]
  norm_num
  rfl

lemma val6 : a 6 = 113451041232 := by
  unfold a; rw [a_Q, a_Q, a_Q, a_Q, a_Q, a_Q]
  simp [Nat.choose]
  norm_num
  rfl

lemma val7 : a 7 = 21790823094272 := by
  unfold a; rw [a_Q, a_Q, a_Q, a_Q, a_Q, a_Q, a_Q]
  simp [Nat.choose]
  norm_num
  rfl

lemma val8 : a 8 = 4339409873332321 := by
  unfold a; rw [a_Q, a_Q, a_Q, a_Q, a_Q, a_Q, a_Q, a_Q]
  simp [Nat.choose]
  norm_num
  rfl

lemma val9 : a 9 = 888730714063587232 := by
  unfold a; rw [a_Q, a_Q, a_Q, a_Q, a_Q, a_Q, a_Q, a_Q, a_Q]
  simp [Nat.choose]
  norm_num
  rfl


lemma a_Q_den_1 : (a_Q 1).den = 1 := by rfl
lemma a_Q_den_2 : (a_Q 2).den = 1 := by
  rw [a_Q, a_Q]; norm_num
lemma a_Q_den_3 : (a_Q 3).den = 1 := by
  rw [a_Q, a_Q, a_Q]; simp [Nat.choose]; norm_num
lemma a_Q_den_4 : (a_Q 4).den = 1 := by rfl
lemma a_Q_den_5 : (a_Q 5).den = 1 := by rfl
lemma a_Q_den_6 : (a_Q 6).den = 1 := by rfl





#print axioms val1

