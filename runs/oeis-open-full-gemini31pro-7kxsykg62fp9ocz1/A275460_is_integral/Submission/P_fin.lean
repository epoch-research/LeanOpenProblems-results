import Submission.Proof
import Submission.Proof_full
import Submission.Rec
import Submission.P3
import Mathlib
open Nat Finset

lemma N_seq_val_sum (n p : ℕ) [hp : Fact p.Prime] :
    padicValNat p (N_seq n) = padicValNat p (3^n) + 
    ∑ i ∈ Icc 1 n, (padicValNat p (9*i - 7) + padicValNat p (9*i - 5) + padicValNat p (9*i - 2)) := by
  induction n with
  | zero => 
    have : N_seq 0 = 1 := rfl
    rw [this, padicValNat.one, pow_zero, padicValNat.one]
    have : Icc 1 0 = ∅ := Icc_eq_empty (by decide)
    rw [this, sum_empty, add_zero]
  | succ n ih =>
    have eq : N_seq (n + 1) = N_seq n * 3 * (9 * (n + 1) - 7) * (9 * (n + 1) - 5) * (9 * (n + 1) - 2) := by
      have : N_seq (n + 1) = N_seq n * 3 * (9 * n + 2) * (9 * n + 4) * (9 * n + 7) := rfl
      rw [this]
      congr 1
      · congr 1
        · congr 1
          omega
        · omega
      · omega
    rw [eq]
    
    have n1 : N_seq n * 3 * (9 * (n + 1) - 7) * (9 * (n + 1) - 5) ≠ 0 := by
      have h1 : N_seq n ≠ 0 := Nat.ne_of_gt (N_seq_pos n)
      have h2 : 3 ≠ 0 := by decide
      have h3 : 9 * (n + 1) - 7 ≠ 0 := by omega
      have h4 : 9 * (n + 1) - 5 ≠ 0 := by omega
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4
    have n2 : 9 * (n + 1) - 2 ≠ 0 := by omega
    rw [padicValNat.mul n1 n2]
    
    have n3 : N_seq n * 3 * (9 * (n + 1) - 7) ≠ 0 := by
      have h1 : N_seq n ≠ 0 := Nat.ne_of_gt (N_seq_pos n)
      have h2 : 3 ≠ 0 := by decide
      have h3 : 9 * (n + 1) - 7 ≠ 0 := by omega
      exact mul_ne_zero (mul_ne_zero h1 h2) h3
    have n4 : 9 * (n + 1) - 5 ≠ 0 := by omega
    rw [padicValNat.mul n3 n4]
    
    have n5 : N_seq n * 3 ≠ 0 := by
      have h1 : N_seq n ≠ 0 := Nat.ne_of_gt (N_seq_pos n)
      have h2 : 3 ≠ 0 := by decide
      exact mul_ne_zero h1 h2
    have n6 : 9 * (n + 1) - 7 ≠ 0 := by omega
    rw [padicValNat.mul n5 n6]
    
    have n7 : N_seq n ≠ 0 := Nat.ne_of_gt (N_seq_pos n)
    have n8 : (3 : ℕ) ≠ 0 := by decide
    rw [padicValNat.mul n7 n8]
    
    have : 1 ≤ n + 1 := by omega
    rw [sum_Icc_succ_top this, ih]
    
    have pow_succ : (3 : ℕ) ^ (n + 1) = 3^n * 3 := by ring
    have h3n : 3^n ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
    rw [pow_succ, padicValNat.mul h3n n8]
    ring

