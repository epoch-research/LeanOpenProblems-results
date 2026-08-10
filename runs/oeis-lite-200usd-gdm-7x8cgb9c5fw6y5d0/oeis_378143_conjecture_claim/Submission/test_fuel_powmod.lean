import FormalConjectures.Util.ProblemImports

def powModAux (base exp mod fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 1 % mod
  | fuel + 1 =>
    if exp = 0 then 1 % mod
    else if exp % 2 = 1 then
      (base * powModAux (base * base % mod) (exp / 2) mod fuel) % mod
    else
      powModAux (base * base % mod) (exp / 2) mod fuel

def powMod (base exp mod : ℕ) : ℕ :=
  powModAux base exp mod exp

theorem powModAux_eq_pow_mod (fuel : ℕ) : ∀ (base exp mod : ℕ), exp ≤ fuel →
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
    · rw [ih (base * base % mod) (exp / 2) mod (by omega)]
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
    · rw [ih (base * base % mod) (exp / 2) mod (by omega)]
      rw [← Nat.pow_mod]
      congr 1
      rw [mul_pow, ← pow_add]
      have h_div_add : exp / 2 + exp / 2 = 2 * (exp / 2) := by omega
      rw [h_div_add]
      have h_eq : 2 * (exp / 2) = exp := by
        have := Nat.div_add_mod exp 2
        omega
      rw [h_eq]

theorem powMod_eq_pow_mod (base exp mod : ℕ) : powMod base exp mod = base ^ exp % mod := by
  unfold powMod
  exact powModAux_eq_pow_mod exp base exp mod (by omega)


