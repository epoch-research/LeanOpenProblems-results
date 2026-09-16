import Mathlib
import Submission.Spec
import Submission.Proof13
import Submission.Proof6

open Nat BigOperators

lemma vp_fact_le (n p : ℕ) [Fact p.Prime] (hn : n > 2) :
  padicValNat p (n - 1).factorial ≤ (n - 2) / (p - 1) := by
  have h1 : (p - 1) * padicValNat p (n - 1).factorial = (n - 1) - (p.digits (n - 1)).sum := by
    exact sub_one_mul_padicValNat_factorial (n - 1)
  have hp_pos : p > 1 := (Fact.out : p.Prime).one_lt
  have hn1_pos : n - 1 > 0 := by omega
  have h2 : (p.digits (n - 1)).sum ≥ 1 := digits_sum_pos p (n - 1) hp_pos hn1_pos
  have h3 : padicValNat p (n - 1).factorial * (p - 1) ≤ n - 2 := by
    calc padicValNat p (n - 1).factorial * (p - 1) = (p - 1) * padicValNat p (n - 1).factorial := by ring
      _ = (n - 1) - (p.digits (n - 1)).sum := h1
      _ ≤ (n - 1) - 1 := by omega
      _ = n - 2 := by omega
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact h3
