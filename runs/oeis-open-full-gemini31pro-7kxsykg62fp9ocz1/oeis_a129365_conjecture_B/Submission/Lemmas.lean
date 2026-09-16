
import Mathlib
open Nat Finset

lemma sum_k_div_k_eq_of_le_2 (x n : ℕ) (hx : x ≤ 2) (hn : x ≤ n) : (Icc 1 n).sum (fun k => k * (x / k)) = x^2 := by
  have eq : (Icc 1 n).sum (fun k => k * (x / k)) = ((Icc 1 n).filter (fun k => k ≤ x)).sum (fun k => k * (x / k)) := by
    apply Eq.symm
    apply sum_subset (filter_subset _ _)
    intro k hk1 hk2
    simp only [mem_filter, hk1, true_and, not_le] at hk2
    have : x / k = 0 := Nat.div_eq_of_lt hk2
    rw [this, mul_zero]
  rw [eq]
  have eq2 : ((Icc 1 n).filter (fun k => k ≤ x)) = Icc 1 x := by
    ext a
    rw [mem_filter, mem_Icc, mem_Icc]
    omega
  rw [eq2]
  have h0 : 0 ≤ x := Nat.zero_le x
  interval_cases x
  · rfl
  · rfl
  · rfl

lemma val_eq_of_le_2 {n p : ℕ} (hp : Fact p.Prime) (hn : 0 < n) (h_p : n / 3 < p) :
    (Icc 1 n).sum (fun e => (Icc 1 n).sum (fun k => k * ((n / p^e) / k))) =
    (Icc 1 n).sum (fun e => (n / p^e) ^ 2) := by
  apply sum_congr rfl
  intro e he
  have h_pos : 0 < p := hp.out.pos
  have h1 : n / p ≤ 2 := by
    -- p > n/3 implies 3*p > n
    -- so n < 3*p, which means n / p < 3.
    apply Nat.lt_succ_iff.mp
    apply Nat.div_lt_of_lt_mul
    have : n / 3 * 3 ≤ n := Nat.div_mul_le_self n 3
    omega
  have h2 : n / p^e ≤ n / p := by
    apply Nat.div_le_div_left
    have h_e : 1 ≤ e := by
      rw [mem_Icc] at he
      exact he.1
    have h_pow : p^1 ≤ p^e := Nat.pow_le_pow_right hp.out.pos h_e
    rwa [pow_one] at h_pow
    positivity
  have hx : n / p^e ≤ 2 := le_trans h2 h1
  have hxn : n / p^e ≤ n := by
    apply Nat.div_le_self
  exact sum_k_div_k_eq_of_le_2 (n / p^e) n hx hxn
