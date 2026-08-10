import FormalConjectures.Util.ProblemImports

def powMod (base exp mod : ℕ) : ℕ :=
  if h : exp = 0 then 1 % mod
  else
    have : exp / 2 < exp := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
    if exp % 2 = 1 then
      (base * powMod (base * base % mod) (exp / 2) mod) % mod
    else
      powMod (base * base % mod) (exp / 2) mod
termination_by exp

#check powMod.induct

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
