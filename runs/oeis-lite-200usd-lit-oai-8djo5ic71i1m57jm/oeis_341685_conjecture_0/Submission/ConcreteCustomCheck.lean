import FormalConjectures.Util.ProblemImports

open Nat

-- Perfect power theorem concrete checks
example : Nat.IsPerfectPower 4 := by
  rw [Nat.isPerfectPower_iff_factorization_gcd]
  native_decide
example : ¬ Nat.IsPerfectPower 2 := by
  rw [Nat.isPerfectPower_iff_factorization_gcd]
  native_decide
example : ¬ Nat.IsPerfectPower 8 := by
  -- should fail: 8 is perfect power
  fail_if_success native_decide
  have : Nat.IsPerfectPower 8 := by
    rw [Nat.isPerfectPower_iff_factorization_gcd]
    native_decide
  exact this.elim

-- Max prime fac concrete checks
example : Nat.maxPrimeFac 2 = 2 := by
  have hp := Nat.maxPrimeFac_eq_of_dvd_of_le 2 2 (by norm_num) (by norm_num) (by norm_num) ?_
  · exact hp
  · rw [Nat.one_lt_maxPrimeFac_iff]; norm_num

example : Nat.maxPrimeFac 4 = 2 := by
  have hp := Nat.maxPrimeFac_eq_of_dvd_of_le 4 2 (by norm_num) (by norm_num) (by norm_num) ?_
  · exact hp
  · have hle : Nat.maxPrimeFac 4 < 3 := by
      -- try compute with theorem?
      sorry
    omega
