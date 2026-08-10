import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 3000000
set_option exponentiation.threshold 1000000


def powModAux (base exp mod fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 1 % mod
  | fuel + 1 =>
    if exp = 0 then 1 % mod
    else if exp % 2 = 1 then
      (base * powModAux (base * base % mod) (exp / 2) mod fuel) % mod
    else
      powModAux (base * base % mod) (exp / 2) mod fuel

theorem powModAux_eq_pow_mod_log (fuel : ℕ) : ∀ (base exp mod : ℕ), exp < 2 ^ fuel →
    powModAux base exp mod fuel = base ^ exp % mod := by
  induction fuel with
  | zero =>
    intro base exp mod h_fuel
    have h_exp : exp = 0 := by omega
    subst h_exp
    unfold powModAux
    rfl
  | succ f ih =>
    intro base exp mod h_fuel
    unfold powModAux
    split_ifs with h_exp h_odd
    · subst h_exp
      rfl
    · have h_div : exp / 2 < 2 ^ f := by
        have h_pow : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
        omega
      rw [ih (base * base % mod) (exp / 2) mod h_div]
      rw [← Nat.pow_mod]
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      congr 1
      rw [mul_pow, ← pow_add]
      have h_div_add : exp / 2 + exp / 2 = 2 * (exp / 2) := by omega
      rw [h_div_add]
      have h_eq : 2 * (exp / 2) + 1 = exp := by
        have := Nat.div_add_mod exp 2
        omega
      conv_rhs => rw [← h_eq]
      rw [pow_succ]
      rw [Nat.mul_comm]
    · have h_div : exp / 2 < 2 ^ f := by
        have h_pow : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
        omega
      rw [ih (base * base % mod) (exp / 2) mod h_div]
      rw [← Nat.pow_mod]
      congr 1
      rw [mul_pow, ← pow_add]
      have h_div_add : exp / 2 + exp / 2 = 2 * (exp / 2) := by omega
      rw [h_div_add]
      have h_eq : 2 * (exp / 2) = exp := by
        have := Nat.div_add_mod exp 2
        omega
      rw [h_eq]

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
  have h_wit : powModAux 3 (10 ^ (2 ^ 13)) (10 ^ (2 ^ 13) + 1) 32768 ≠ 1 := by
    decide
  have h_less : 10 ^ (2 ^ 13) < 2 ^ 32768 := by
    -- We can prove this by comparing 10 with 16:
    -- 10 ^ 8192 < 16 ^ 8192 = (2 ^ 4) ^ 8192 = 2 ^ 32768
    have h10 : 10 < 16 := by decide
    have h_pow : 10 ^ (2 ^ 13) < 16 ^ (2 ^ 13) := Nat.pow_lt_pow_left h10 (by decide)
    have h16 : (16 : ℕ) = 2 ^ 4 := by decide
    rw [h16] at h_pow
    rw [← pow_mul] at h_pow
    have h_mul : 4 * 2 ^ 13 = 32768 := by decide
    rwa [h_mul] at h_pow
  rw [powModAux_eq_pow_mod_log 32768 3 (10 ^ (2 ^ 13)) (10 ^ (2 ^ 13) + 1) h_less] at h_wit
  exact not_prime_of_fermat_witness_nat (10 ^ (2 ^ 13) + 1) 3 hp (by decide) (by decide) h_wit
