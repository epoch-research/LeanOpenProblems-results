import Submission.Spec
import Mathlib.Tactic

open Nat Rat Finset

set_option maxRecDepth 200000

lemma div_5 : Nat.divisors 5 = {1, 5} := by decide

lemma val_5 : sum_divisors_inv_pow 5 31 1 = 17 / 288 := by
  unfold sum_divisors_inv_pow
  rw [div_5]
  norm_num

lemma div_1829 : Nat.divisors 1829 = {1, 31, 59, 1829} := by decide

lemma val_1829 : sum_divisors_inv_pow 1829 31 1 = 17 / 288 := by
  unfold sum_divisors_inv_pow
  rw [div_1829]
  norm_num

lemma disproof_lemma : ¬ (∀ (k s : ℕ), k > 0 ∧ s > 0 →
  (∀ n : ℕ, n > 0 →
    (Int.fract (sum_divisors_inv_pow n k s) ≠ 0))
  ∧
  (∀ n₁ n₂ : ℕ, n₁ > 0 → n₂ > 0 → Int.fract (sum_divisors_inv_pow n₁ k s) = Int.fract (sum_divisors_inv_pow n₂ k s) → n₁ = n₂)) := by
  intro h
  have h_k_s := h 31 1 (by decide)
  have h_inj := h_k_s.2
  have h_eq : Int.fract (sum_divisors_inv_pow 5 31 1) = Int.fract (sum_divisors_inv_pow 1829 31 1) := by
    rw [val_5, val_1829]
  have h_n_eq := h_inj 5 1829 (by decide) (by decide) h_eq
  revert h_n_eq
  decide
