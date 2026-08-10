import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option exponentiation.threshold 100000

def pow10ModAux (M : ℕ) : ℕ → ℕ → ℕ
  | 0, val => val
  | k + 1, val => pow10ModAux M k (val ^ 10 % M)

theorem pow10ModAux_eq (M : ℕ) (k : ℕ) (val : ℕ) :
    pow10ModAux M k val % M = val ^ (10 ^ k) % M := by
  induction k generalizing val with
  | zero =>
    simp [pow10ModAux]
  | succ k ih =>
    simp [pow10ModAux]
    rw [ih]
    rw [← Nat.pow_mod]
    congr 1
    rw [← pow_mul, ← pow_succ]

theorem not_prime_of_fermat_witness_nat (N a : ℕ) (h_prime : Nat.Prime N) (ha : a < N) (ha1 : 1 < a)
    (h_witness : a ^ (N - 1) % N ≠ 1) : False := by
  have h_fact : Fact N.Prime := ⟨h_prime⟩
  have h_ne : (a : ZMod N) ≠ 0 := by
    rw [← ZMod.val_ne_zero]
    rw [ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt ha]
    exact Nat.ne_of_gt (by lia)
  have h_one : (a : ZMod N) ^ (N - 1) = 1 := @ZMod.pow_card_sub_one_eq_one N h_fact a h_ne
  have h_cast : ((a ^ (N - 1) : ℕ) : ZMod N) = 1 := by
    rw [Nat.cast_pow]
    exact h_one
  have h_val : (((a ^ (N - 1) : ℕ) : ZMod N)).val = (1 : ZMod N).val := by rw [h_cast]
  rw [ZMod.val_natCast, ZMod.val_one] at h_val
  exact h_witness h_val

theorem not_prime_13 : ¬ Nat.Prime (10 ^ (2 ^ 13) + 1) := by
  intro hp
  have h_wit : pow10ModAux (10 ^ (2 ^ 13) + 1) 8192 3 % (10 ^ (2 ^ 13) + 1) ≠ 1 := by
    decide
  have h_pow_eq : 2 ^ 13 = 8192 := by decide
  rw [h_pow_eq] at hp
  have h_eq := pow10ModAux_eq (10 ^ 8192 + 1) 8192 3
  rw [h_eq] at h_wit
  exact not_prime_of_fermat_witness_nat (10 ^ 8192 + 1) 3 hp (by decide) (by decide) h_wit
