import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 10000

private def powChunk (a m e : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | f+1 => ((a ^ (e % 256)) * powChunk ((a ^ 256) % m) m (e / 256) f) % m

private lemma chunk_pow_mod (a m q : ℕ) :
    ((a ^ 256) % m) ^ q % m = (a ^ q) ^ 256 % m := by
  rw [← Nat.pow_mod (a ^ 256) q m]
  rw [← pow_mul]
  rw [show 256 * q = q * 256 by omega]
  rw [← pow_mul]

private lemma powChunk_eq (a m e f : ℕ) (hbound : e < 256 ^ f) :
    powChunk a m e f = a ^ e % m := by
  induction f generalizing a e with
  | zero =>
      have he : e = 0 := by norm_num at hbound; omega
      subst e
      simp [powChunk]
  | succ f ih =>
      have hdivbound : e / 256 < 256 ^ f := by
        have hpow : 256 ^ (f + 1) = 256 * 256 ^ f := by rw [pow_succ']
        rw [hpow] at hbound
        exact Nat.div_lt_of_lt_mul hbound
      simp [powChunk]
      rw [ih ((a ^ 256) % m) (e / 256) hdivbound]
      have heq : e = e % 256 + 256 * (e / 256) := by
        have h := Nat.div_add_mod e 256
        omega
      have hdiv : (e % 256 + 256 * (e / 256)) / 256 = e / 256 := by
        have hmodlt : e % 256 < 256 := Nat.mod_lt e (by norm_num)
        omega
      rw [heq]
      simp [hdiv, pow_add, pow_mul, Nat.mul_mod, Nat.mul_comm]
      rw [chunk_pow_mod a m (e / 256)]
      rw [show (a ^ (e / 256)) ^ 256 = (a ^ 256) ^ (e / 256) by
        rw [← pow_mul, ← pow_mul, show e / 256 * 256 = 256 * (e / 256) by omega]]


example : powChunk 2 17 5 1 = 15 := by decide
example : powChunk 2 17 5 1 = 2 ^ 5 % 17 := powChunk_eq _ _ _ _ (by norm_num)
