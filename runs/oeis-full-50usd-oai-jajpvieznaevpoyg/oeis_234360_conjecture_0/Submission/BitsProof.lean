import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private def evalBits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * evalBits bs

private def powBits (a m : ℕ) : List Bool → ℕ
  | [] => 1 % m
  | b :: bs => ((if b then a else 1) * powBits ((a * a) % m) m bs) % m


private lemma sq_pow_mod (a m e : ℕ) : ((a * a) % m) ^ e % m = (a ^ e) ^ 2 % m := by
  rw [← Nat.pow_mod (a * a) e m]
  rw [mul_pow]
  rw [pow_two]


private lemma sq_pow_mod' (x m e : ℕ) :
    ((x % m * (x % m)) % m % m) ^ e % m = (((x % m) ^ e % m % m) ^ 2) % m := by
  rw [Nat.mod_mod]
  rw [← Nat.pow_mod ((x % m) * (x % m)) e m]
  rw [mul_pow]
  rw [pow_two]
  simp [Nat.mul_mod, Nat.mod_mod]


private lemma sq_pow_mod'' (x m e : ℕ) :
    ((x % m % m * (x % m % m)) % m % m) ^ e % m = (((x % m % m) ^ e % m % m) ^ 2) % m := by
  rw [sq_pow_mod' (x % m) m e]


private lemma sq_pow_mod_goal (x m e : ℕ) :
    ((x % m % m * (x % m % m)) % m) ^ e % m = (x ^ e) ^ 2 % m := by
  rw [← Nat.pow_mod ((x % m % m) * (x % m % m)) e m]
  rw [mul_pow]
  rw [pow_two]
  simp [Nat.pow_mod, Nat.mul_mod, Nat.mod_mod]





private lemma powBits_eq (a m : ℕ) (bs : List Bool) :
    powBits a m bs = a ^ (evalBits bs) % m := by
  induction bs generalizing a with
  | nil => simp [powBits, evalBits]
  | cons b bs ih =>
      simp [powBits, evalBits, ih]
      cases b
      · simp [Bool.toNat, pow_add, pow_mul, Nat.mul_mod, Nat.mul_comm]
        rw [sq_pow_mod_goal a m (evalBits bs)]
      · simp [Bool.toNat, pow_add, pow_mul, Nat.mul_mod, Nat.mul_comm]
        rw [sq_pow_mod_goal a m (evalBits bs)]

example : evalBits [true,false,true] = 5 := by decide
example : powBits 2 17 [true,false,true] = 15 := by decide
