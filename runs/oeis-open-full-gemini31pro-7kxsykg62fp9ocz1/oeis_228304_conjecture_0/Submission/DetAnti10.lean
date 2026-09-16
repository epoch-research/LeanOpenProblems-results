import Mathlib
import Submission.DetAnti9
import Submission.Defs

open Nat Finset

lemma sum_neg_one_pow {p : ℕ} [NeZero p] (m : ℕ) : ∑ k ∈ range (2 * m + 1), (-1 : ZMod p)^k = 1 := by
  induction' m with m ih
  · simp
  · rw [mul_add, mul_one]
    -- 2 * (m + 1) + 1 = 2 * m + 1 + 2
    have H : 2 * m + 2 + 1 = 2 * m + 1 + 2 := by ring
    rw [H, sum_range_add]
    have H1 : (-1 : ZMod p)^(2 * m + 1 + 0) = -1 := by
      have : 2 * m + 1 + 0 = 2 * m + 1 := by omega
      rw [this, pow_add, pow_mul, pow_one]
      have : (-1 : ZMod p)^2 = 1 := by simp
      rw [this, one_pow, one_mul]
    have H2 : (-1 : ZMod p)^(2 * m + 1 + 1) = 1 := by
      have : 2 * m + 1 + 1 = 2 * m + 2 := by omega
      rw [this, pow_add, pow_mul]
      have : (-1 : ZMod p)^2 = 1 := by simp
      rw [this, one_pow, mul_one]
    simp [sum_range_succ, H1, H2, ih]

lemma a_p_minus_1_mod_p (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) :
    (a_val (p - 1) : ZMod p) = 1 := by
  have h_p_pos : 0 < p := hp.out.pos
  have H1 : (a_val (p - 1) : ZMod p) = ∑ k ∈ range p, (-1 : ZMod p)^k * (choose (p - 1) k : ZMod p)^4 := by
    dsimp [a_val]
    have : p - 1 + 1 = p := by omega
    have h_range : range (p - 1 + 1) = range p := by rw [this]
    rw [h_range]
    push_cast
    rfl
  rw [H1]
  have H2 : ∑ k ∈ range p, (-1 : ZMod p)^k * (choose (p - 1) k : ZMod p)^4 = ∑ k ∈ range p, (-1 : ZMod p)^k := by
    apply sum_congr rfl
    intro k hk
    have hk_lt : k < p := mem_range.mp hk
    rw [choose_p_minus_one_mod_p p k hk_lt]
    have : ((-1 : ZMod p)^k)^4 = 1 := by
      rw [← pow_mul]
      have : k * 4 = 2 * (2 * k) := by ring
      rw [this, pow_mul]
      have : (-1 : ZMod p)^2 = 1 := by simp
      rw [this, one_pow]
    rw [this, mul_one]
  rw [H2]
  have h_odd : p % 2 = 1 := by
    cases hp.out.eq_two_or_odd with
    | inl h2 => exfalso; exact hp_odd h2
    | inr hodd => exact hodd
  have h_p_eq : p = 2 * (p / 2) + 1 := by omega
  have h_range2 : range p = range (2 * (p / 2) + 1) := by
    nth_rewrite 1 [h_p_eq]
    rfl
  rw [h_range2]
  exact sum_neg_one_pow (p / 2)
