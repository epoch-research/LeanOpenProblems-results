import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option exponentiation.threshold 100000

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
  apply not_prime_of_fermat_witness_nat (10 ^ (2 ^ 13) + 1) 3 hp (by decide) (by decide)
  decide


