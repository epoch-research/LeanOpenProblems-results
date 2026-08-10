import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private def powFuel (a m e : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | f+1 => ((if e % 2 = 1 then a else 1) * powFuel ((a * a) % m) m (e / 2) f) % m

private lemma sq_pow_mod_goal (x m e : ℕ) :
    ((x % m % m * (x % m % m)) % m) ^ e % m = (x ^ e) ^ 2 % m := by
  rw [← Nat.pow_mod ((x % m % m) * (x % m % m)) e m]
  rw [mul_pow]
  rw [pow_two]
  simp [Nat.pow_mod, Nat.mul_mod]

private lemma powFuel_eq (a m e f : ℕ) (hbound : e < 2 ^ f) :
    powFuel a m e f = a ^ e % m := by
  induction f generalizing a e with
  | zero =>
      have he : e = 0 := by omega
      subst e
      simp [powFuel]
  | succ f ih =>
      have hdivbound : e / 2 < 2 ^ f := by
        have h2 : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [pow_succ']
        rw [h2] at hbound
        exact Nat.div_lt_of_lt_mul hbound
      simp [powFuel]
      rw [ih ((a * a) % m) (e / 2) hdivbound]
      have hmodlt : e % 2 = 0 ∨ e % 2 = 1 := by omega
      rcases hmodlt with h0 | h1
      · have heven : e = 2 * (e / 2) := by
          have h := Nat.div_add_mod e 2
          omega
        rw [heven]
        simp [h0, pow_mul, Nat.mul_mod, Nat.mul_comm]
        rw [sq_pow_mod_goal a m (e / 2)]
        rw [show (a ^ (e / 2)) ^ 2 = (a ^ 2) ^ (e / 2) by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      · have hodd : e = 1 + 2 * (e / 2) := by
          have h := Nat.div_add_mod e 2
          omega
        have hdiv : (1 + 2 * (e / 2)) / 2 = e / 2 := by omega
        rw [hodd]
        simp [h1, hdiv, pow_add, pow_mul, Nat.mul_mod, Nat.mul_comm]
        rw [sq_pow_mod_goal a m (e / 2)]
        rw [show (a ^ (e / 2)) ^ 2 = (a ^ 2) ^ (e / 2) by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]

example : powFuel 2 17 5 3 = 15 := by decide
example : powFuel 2 17 5 3 = 2 ^ 5 % 17 := powFuel_eq _ _ _ _ (by norm_num)
