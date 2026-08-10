import FormalConjectures.Util.ProblemImports

open Nat

theorem sum_digits_add_le (p a b : ℕ) [hp : Fact p.Prime] :
    (p.digits (a + b)).sum ≤ (p.digits a).sum + (p.digits b).sum := by
  have h_le := Nat.le_add_left a b
  have h_kummer := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (hp := hp) h_le
  rw [Nat.add_sub_cancel b a] at h_kummer
  rw [add_comm b a] at h_kummer
  omega

