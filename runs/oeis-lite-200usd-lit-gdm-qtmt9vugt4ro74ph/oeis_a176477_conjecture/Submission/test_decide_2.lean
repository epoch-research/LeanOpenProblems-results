import Submission.Spec

open Nat

def is_pow2_bounded (n : ℕ) : Prop :=
  ∃ m < n + 1, m ≥ 1 ∧ n = 2^m

instance (n : ℕ) : Decidable (is_pow2_bounded n) :=
  inferInstance

theorem is_pow2_iff (n : ℕ) : (∃ m : ℕ, m ≥ 1 ∧ n = 2^m) ↔ is_pow2_bounded n := by
  unfold is_pow2_bounded
  constructor
  · rintro ⟨m, hm1, hm2⟩
    have h_lt : m < n + 1 := by
      have : n = 2^m := hm2
      have h_gt : 2^m ≥ m + 1 := Nat.lt_pow_self (by omega)
      omega
    use m, h_lt, hm1, hm2
  · rintro ⟨m, hm_lt, hm1, hm2⟩
    use m

def P (n : ℕ) : Prop :=
  a n > 0 ∧ (Odd (a n) ↔ is_pow2_bounded n)

instance (n : ℕ) : Decidable (P n) := by
  unfold P
  infer_instance

theorem p9 : P 9 := by
  decide
