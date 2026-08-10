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
