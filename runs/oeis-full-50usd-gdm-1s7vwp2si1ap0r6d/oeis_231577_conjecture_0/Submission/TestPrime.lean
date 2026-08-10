import FormalConjectures.Util.ProblemImports

open Nat

def powModAux (base exp mod fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 1 % mod
  | fuel' + 1 =>
    if exp = 0 then 1 % mod
    else
      let half := powModAux base (exp / 2) mod fuel'
      let square := (half * half) % mod
      if exp % 2 = 1 then (square * base) % mod
      else square

def powMod (base exp mod : ℕ) : ℕ :=
  powModAux base exp mod 40


theorem mod_mul_mod_helper (A B C m : ℕ) : ((A % m * (B % m)) * C) % m = (A * B * C) % m := by
  rw [Nat.mul_mod, ← Nat.mul_mod A B m, ← Nat.mul_mod]

theorem mod_mul_mod_helper2 (A B m : ℕ) : ((A % m * (B % m)) % m) = (A * B) % m := by
  rw [← Nat.mul_mod]

theorem powMod_test : powMod 2 3565431 5 = 3 := by
  decide


















