import FormalConjectures.Util.ProblemImports

open Nat

-- n=13, k=213
-- m = 1594110
-- A = 13058949119, A-1 = 2 * 6143 * 1062913, witness 13
-- B = 13058949121, B-1 = 2^14 * 3 * 5 * 7 * 7591, witness 17

lemma prime_7591 : Nat.Prime 7591 := by norm_num
lemma prime_6143 : Nat.Prime 6143 := by norm_num
lemma prime_1062913 : Nat.Prime 1062913 := by norm_num

set_option maxRecDepth 100000
lemma b_pow_nat : (17 : ℕ) ^ (13058949121 - 1) % 13058949121 = 1 := by
  native_decide

lemma b_pow : (17 : ZMod 13058949121) ^ (13058949121 - 1) = 1 := by
  rw [← ZMod.natCast_mod, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  -- better approach
  apply ZMod.natCast_eq_natCast_iff.mpr
  change (17 : ℕ) ^ (13058949121 - 1) ≡ 1 [MOD 13058949121]
  rw [Nat.ModEq]
  native_decide

#check lucas_primality
