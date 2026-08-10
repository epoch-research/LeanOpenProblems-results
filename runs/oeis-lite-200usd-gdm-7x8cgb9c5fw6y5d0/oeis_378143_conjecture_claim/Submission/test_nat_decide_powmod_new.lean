import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option exponentiation.threshold 100000

def powMod (base exp mod : ℕ) : ℕ :=
  if h : exp = 0 then 1 % mod
  else
    have : exp / 2 < exp := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    if exp % 2 = 1 then
      (base * powMod (base * base % mod) (exp / 2) mod) % mod
    else
      powMod (base * base % mod) (exp / 2) mod
termination_by exp

theorem powMod_eq_pow_mod (base exp mod : ℕ) : powMod base exp mod = base ^ exp % mod := by
  induction base, exp using powMod.induct mod with
  | case1 base =>
    unfold powMod
    rfl
  | case2 base exp h h_div h_odd ih =>
    unfold powMod
    rw [dif_neg h, if_pos h_odd]
    rw [ih]
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
  | case3 base exp h h_div h_even ih =>
    unfold powMod
    rw [dif_neg h, if_neg h_even]
    rw [ih]
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

theorem not_prime_of_powMod_witness (N a : ℕ) (h_prime : Nat.Prime N) (ha : a < N) (ha1 : 1 < a)
    (h_witness : powMod a (N - 1) N ≠ 1) : False := by
  apply not_prime_of_fermat_witness_nat N a h_prime ha ha1
  rwa [powMod_eq_pow_mod] at h_witness

theorem not_prime_13 : ¬ Nat.Prime (10 ^ (2 ^ 13) + 1) := by
  intro hp
  apply not_prime_of_powMod_witness (10 ^ (2 ^ 13) + 1) 3 hp (by decide) (by decide)
  decide
