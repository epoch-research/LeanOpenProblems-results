import Submission.Rec
import Mathlib
open Nat Finset

lemma val3_mul_not_div (x y : ℕ) (hx : x > 0) (hy : ¬ 3 ∣ y) : padicValNat 3 (x * y) = padicValNat 3 x := by
  have hp : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hy0 : y ≠ 0 := by
    intro h
    subst h
    have : 3 ∣ 0 := dvd_zero 3
    exact hy this
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  rw [padicValNat.mul hx0 hy0, padicValNat.eq_zero_of_not_dvd hy, add_zero]

lemma not_dvd_3_of_mod_not_zero (x : ℕ) (h : x % 3 ≠ 0) : ¬ 3 ∣ x := by
  intro hdvd
  have : x % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  exact h this

lemma val3_N_seq (n : ℕ) : padicValNat 3 (N_seq n) = n := by
  induction n with
  | zero => 
    have : N_seq 0 = 1 := rfl
    rw [this, padicValNat.one]
  | succ n ih =>
    have eq : N_seq (n + 1) = N_seq n * 3 * (9 * n + 2) * (9 * n + 4) * (9 * n + 7) := rfl
    rw [eq]
    have hp : Fact (Nat.Prime 3) := ⟨by decide⟩
    have h1 : ¬ 3 ∣ (9 * n + 7) := not_dvd_3_of_mod_not_zero _ (by omega)
    have pos1 : N_seq n * 3 * (9 * n + 2) * (9 * n + 4) > 0 := by
      have := N_seq_pos n; positivity
    rw [val3_mul_not_div _ _ pos1 h1]
    
    have h2 : ¬ 3 ∣ (9 * n + 4) := not_dvd_3_of_mod_not_zero _ (by omega)
    have pos2 : N_seq n * 3 * (9 * n + 2) > 0 := by
      have := N_seq_pos n; positivity
    rw [val3_mul_not_div _ _ pos2 h2]
    
    have h3 : ¬ 3 ∣ (9 * n + 2) := not_dvd_3_of_mod_not_zero _ (by omega)
    have pos3 : N_seq n * 3 > 0 := by
      have := N_seq_pos n; positivity
    rw [val3_mul_not_div _ _ pos3 h3]
    
    have ne_N : N_seq n ≠ 0 := Nat.ne_of_gt (N_seq_pos n)
    rw [padicValNat.mul ne_N (by decide), ih]
    have : padicValNat 3 3 = 1 := padicValNat_self
    rw [this]

lemma val3_D (n : ℕ) : padicValNat 3 (D n) = 2 * padicValNat 3 (Nat.factorial n) := by
  induction n with
  | zero => 
    have : D 0 = 1 := rfl
    rw [this, padicValNat.one]
    have hf : padicValNat 3 (Nat.factorial 0) = 0 := padicValNat.one
    rw [hf]
  | succ n ih =>
    have eq : D (n + 1) = D n * (n + 1)^2 * (3 * n + 1) := rfl
    rw [eq]
    have hp : Fact (Nat.Prime 3) := ⟨by decide⟩
    have h1 : ¬ 3 ∣ (3 * n + 1) := not_dvd_3_of_mod_not_zero _ (by omega)
    have pos1 : D n * (n + 1)^2 > 0 := by
      have := D_pos n; positivity
    rw [val3_mul_not_div _ _ pos1 h1]
    
    have ne_D : D n ≠ 0 := Nat.ne_of_gt (D_pos n)
    have pos_succ : (n + 1)^2 > 0 := by positivity
    have ne_succ : (n + 1)^2 ≠ 0 := Nat.ne_of_gt pos_succ
    rw [padicValNat.mul ne_D ne_succ, ih]
    
    have ne_succ2 : n + 1 ≠ 0 := by positivity
    have hp_pow : Fact (Nat.Prime 3) := ⟨by decide⟩
    have eq_pow : padicValNat 3 ((n + 1)^2) = 2 * padicValNat 3 (n + 1) := by
      exact padicValNat.pow 2 ne_succ2
    rw [eq_pow]
    have eq_fact : padicValNat 3 (Nat.factorial (n + 1)) = padicValNat 3 (Nat.factorial n) + padicValNat 3 (n + 1) := by
      rw [Nat.factorial_succ, padicValNat.mul ne_succ2 (factorial_ne_zero n), add_comm]
    rw [eq_fact]
    ring

lemma padicValNat_three_factorial_le (n : ℕ) : 2 * padicValNat 3 (Nat.factorial n) ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hp : Fact (Nat.Prime 3) := ⟨by decide⟩
    have h : (3 - 1) * padicValNat 3 (Nat.factorial n) < n := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 3 hn
    exact h.le

lemma val3_le (n : ℕ) : padicValNat 3 (D n) ≤ padicValNat 3 (N_seq n) := by
  rw [val3_D, val3_N_seq]
  exact padicValNat_three_factorial_le n
