import Mathlib

open Nat

set_option exponentiation.threshold 100000
set_option maxRecDepth 200000

theorem test_coprime : 3.Coprime (10 ^ 8192 + 1) := by
  have hp : Nat.Prime 3 := by decide
  have h_not_dvd : ¬ 3 ∣ 10 ^ 8192 + 1 := by decide
  exact hp.coprime_iff_not_dvd.mpr h_not_dvd
