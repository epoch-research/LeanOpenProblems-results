import FormalConjectures.Util.ProblemImports
open Nat
open Rat

noncomputable def A022030_original (n : ℕ) : ℕ :=
  if h0 : n = 0 then 4
  else if h1 : n = 1 then 16
  else
    let b_n_1 := A022030_original (n - 1)
    let b_n_2 := A022030_original (n - 2)
    let num := b_n_1 ^ 2
    let den := b_n_2
    (num + den - 1) / den - 1
termination_by n


private def B : ℕ → ℕ
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * B (n + 2) - B n

private lemma B_pos_double (n : ℕ) : 0 < B n ∧ 2 * B n ≤ B (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · norm_num [B]
    · norm_num [B]
    · norm_num [B]
    · have hk2 := ih (k + 2) (by omega)
      have hk1 := ih (k + 1) (by omega)
      constructor
      · nlinarith [hk2.1, hk2.2]
      · change 2 * B (k + 3) ≤ 4 * B (k + 3) - B (k + 1)
        have : B (k + 1) ≤ 2 * B (k + 3) := by nlinarith [hk1.1, hk1.2, hk2.1, hk2.2]
        omega

private lemma B_pos (n : ℕ) : 0 < B n := (B_pos_double n).1
private lemma B_double (n : ℕ) : 2 * B n ≤ B (n + 1) := (B_pos_double n).2

private lemma B_rec_add (n : ℕ) : B (n + 3) + B n = 4 * B (n + 2) := by
  change (4 * B (n + 2) - B n) + B n = 4 * B (n + 2)
  have h : B n ≤ 4 * B (n + 2) := by
    have h0 := B_pos n
    have h1 := B_double n
    have h2 := B_double (n+1)
    nlinarith
  omega

private def R : ℕ → ℕ
  | 0 => 4
  | 1 => 1
  | 2 => 16
  | n + 3 => 4 * R (n + 1) + R n

private lemma R_pos_bound (n : ℕ) : 0 < R n ∧ R n ≤ B n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · norm_num [R, B]
    · norm_num [R, B]
    · norm_num [R, B]
    · have hk := ih k (by omega)
      have hk1 := ih (k+1) (by omega)
      have hbrec := B_rec_add k
      constructor
      · change 0 < 4 * R (k + 1) + R k
        nlinarith [hk.1]
      · change 4 * R (k + 1) + R k ≤ B (k + 3)
        have hb1 := B_double k
        have hb2 := B_double (k+1)
        nlinarith

private lemma R_pos (n : ℕ) : 0 < R n := (R_pos_bound n).1
private lemma R_bound (n : ℕ) : R n ≤ B n := (R_pos_bound n).2

private lemma R_rel (n : ℕ) : B (n + 1) ^ 2 = B n * B (n + 2) + R n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · norm_num [B, R]
    · norm_num [B, R]
    · norm_num [B, R]
    · have ih0 := ih k (by omega)
      have ih1 := ih (k+1) (by omega)
      have hrec0 := B_rec_add k
      have hrec1 := B_rec_add (k+1)
      have hrec2 := B_rec_add (k+2)
      change B (k + 4) ^ 2 = B (k + 3) * B (k + 5) + (4 * R (k + 1) + R k)
      nlinarith


private lemma ceil_pred_div {q d r : ℕ} (_hd : 0 < d) (hr0 : 0 < r) (hrle : r ≤ d) :
    ((q * d + r + d - 1) / d - 1 = q) := by
  have hle' : q * d + d ≤ q * d + r + d - 1 := by omega
  have hle : (q + 1) * d ≤ q * d + r + d - 1 := by
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle'
  have hlt' : q * d + r + d - 1 < q * d + (d + d) := by omega
  have hlt : q * d + r + d - 1 < (q + 2) * d := by
    simpa [Nat.add_mul, Nat.succ_mul, Nat.one_mul, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt'
  have hdiv : (q * d + r + d - 1) / d = q + 1 := Nat.div_eq_of_lt_le hle hlt
  omega

private lemma A_eq_B (n : ℕ) : A022030_original n = B n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · simp [A022030_original.eq_def, B]
    · simp [A022030_original.eq_def, B]
    · have ih1 := ih (k + 1) (by omega)
      have ih2 := ih k (by omega)
      rw [A022030_original.eq_def]
      simp only [Nat.add_eq, OfNat.ofNat_ne_zero, reduceCtorEq, dite_false, ite_false]
      change (A022030_original (k + 2 - 1) ^ 2 + A022030_original (k + 2 - 2) - 1) /
            A022030_original (k + 2 - 2) - 1 = B (k + 2)
      rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
      rw [ih1, ih2]
      rw [R_rel k]
      rw [Nat.mul_comm (B k) (B (k + 2))]
      exact ceil_pred_div (B_pos k) (R_pos k) (R_bound k)

theorem oeis_22030_original_conjecture (n : ℕ) :
  A022030_original n = (
    if n = 0 then 4
    else if n = 1 then 16
    else if n = 2 then 63
    else
      4 * (A022030_original (n - 1)) - (A022030_original (n - 3))
  ) :=
by
  rw [A_eq_B n]
  rcases n with _ | _ | _ | k
  · simp [B]
  · simp [B]
  · simp [B]
  · rw [A_eq_B (k + 3 - 1), A_eq_B (k + 3 - 3)]
    simp [B]

