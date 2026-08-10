import FormalConjectures.Util.ProblemImports

open Nat

#check Nat.ModEq
#check Nat.ModEq.iff_dvd
#check Nat.modEq_iff_dvd
#check Nat.ModEq

def powMod : ℕ → ℕ → ℕ → ℕ
  | a, 0, m => 1 % m
  | a, e+1, m => (a * powMod a e m) % m

lemma powMod_eq (a e m : ℕ) : powMod a e m = a ^ e % m := by
  induction e with
  | zero => simp [powMod]
  | succ e ih =>
      simp [powMod, pow_succ, ih, Nat.mul_mod, Nat.mul_comm]

example : powMod 2 1000 7 = 2^1000 % 7 := powMod_eq _ _ _
