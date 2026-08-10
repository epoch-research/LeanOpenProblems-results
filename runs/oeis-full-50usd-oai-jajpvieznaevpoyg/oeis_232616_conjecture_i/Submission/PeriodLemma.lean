import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 30000

open Nat

theorem pow_period_odd : 2^29400 ≡ 1 [MOD 137543] := by
  native_decide
#print axioms pow_period_odd

example (t : Nat) : (2^29400)^t ≡ 1 [MOD 137543] := by
  exact Nat.ModEq.pow t pow_period_odd

example (a t : Nat) (ha : 2 ≤ a) : 2^(a + t*29400) ≡ 2^a [MOD 550172] := by
  have hodd : (2^29400)^t ≡ 1 [MOD 137543] := Nat.ModEq.pow t pow_period_odd
  have hodd2 : 2^(t*29400) ≡ 1 [MOD 137543] := by
    rw [mul_comm t 29400, pow_mul]
    exact hodd
  have hodd3 : 2^a * 2^(t*29400) ≡ 2^a * 1 [MOD 137543] := hodd2.mul_left _
  have hodd4 : 2^(a+t*29400) ≡ 2^a [MOD 137543] := by
    rw [pow_add, mul_one] at hodd3
    exact hodd3
  -- need combine mod 4 and 137543
  have h4lhs : 4 ∣ 2^(a+t*29400) := by
    rw [show 4 = 2^2 by norm_num]
    exact pow_dvd_pow 2 (by omega)
  have h4rhs : 4 ∣ 2^a := by
    rw [show 4 = 2^2 by norm_num]
    exact pow_dvd_pow 2 ha
  have h4 : 2^(a+t*29400) ≡ 2^a [MOD 4] := by
    rw [Nat.modEq_zero_iff_dvd.mpr h4lhs, Nat.modEq_zero_iff_dvd.mpr h4rhs]
  have hcrt : 4 * 137543 ∣ (2^(a+t*29400) : Int) - (2^a : Int) := by
    sorry
  rw [show 550172 = 4 * 137543 by norm_num]
  rw [Nat.modEq_iff_dvd]
  exact hcrt
