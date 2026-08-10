import FormalConjectures.Util.ProblemImports
open Nat

lemma land_mod_two_pow (a M r : Nat) :
    ((a &&& M) % 2^r) = (((a % 2^r) &&& (M % 2^r))) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < r
  · simp [Nat.testBit_mod_two_pow, hi]
  · simp [Nat.testBit_mod_two_pow, hi]

lemma land_congr_mod_two_pow {a b M r : Nat} (h : a % 2^r = b % 2^r) :
    ((a &&& M) % 2^r) = ((b &&& M) % 2^r) := by
  rw [land_mod_two_pow a M r, land_mod_two_pow b M r, h]
