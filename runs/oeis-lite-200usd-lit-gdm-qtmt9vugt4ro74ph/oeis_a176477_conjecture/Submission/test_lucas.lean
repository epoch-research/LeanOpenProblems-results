import Mathlib.Data.Nat.Choose.Lucas

open Nat

example (n k : ℕ) : choose n k ≡ choose (n % 2) (k % 2) * choose (n / 2) (k / 2) [MOD 2] := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat
