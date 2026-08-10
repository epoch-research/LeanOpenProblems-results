import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000

open Nat ArithmeticFunction Rat

theorem sigma_one_mul_coprime (a b : ℕ) (h : Coprime a b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b := by
  exact isMultiplicative_sigma.map_mul_of_coprime h

theorem nat_div_eq_divInt (a b : ℕ) : ((a : ℚ) / (b : ℚ)) = (a : ℤ) /. (b : ℤ) := by
  rw [Rat.divInt_eq_div]
  push_cast
  rfl

theorem coprime_num_den (a b : ℕ) (hb : 0 < b) (h_cop : Coprime a b) :
    (((a : ℤ) /. (b : ℤ)).num = a) ∧ (((a : ℤ) /. (b : ℤ)).den = b) := by
  have h_gcd : Int.gcd b a = 1 := by
    have h1 : (b : ℤ).natAbs = b := rfl
    have h2 : (a : ℤ).natAbs = a := rfl
    simp [Int.gcd, h1, h2]
    exact h_cop.symm
  have h_sign : Int.sign b = 1 := by
    rw [Int.sign_eq_one_of_pos]
    omega
  constructor
  · rw [Rat.num_divInt]
    rw [h_gcd, h_sign]
    simp
  · rw [Rat.den_divInt]
    have hb_ne : (b : ℤ) ≠ 0 := by omega
    rw [if_neg hb_ne]
    rw [h_gcd]
    simp

def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

theorem prime_k_case (n : ℕ) (k : ℕ) (hk : k.Prime) (hn : 2 < n) (hp : (k * (n - 1) - 1).Prime) (h_cop : Coprime k (k * (n - 1) - 1)) :
    A243473_val (k * (k * (n - 1) - 1)) = n := by
  unfold A243473_val
  have hk_pos : 0 < k := hk.pos
  have h_p_pos : 0 < k * (n - 1) - 1 := hp.pos
  have hi_ne_zero : k * (k * (n - 1) - 1) ≠ 0 := Nat.mul_ne_zero hk_pos.ne' h_p_pos.ne'
  rw [if_neg hi_ne_zero]
  have h_sigma_k : sigma 1 k = k + 1 := by
    rw [sigma_apply, Nat.Prime.divisors hk]
    simp
  have h_sigma_p : sigma 1 (k * (n - 1) - 1) = k * (n - 1) := by
    rw [sigma_apply, Nat.Prime.divisors hp]
    simp
  have h_sigma_mul : sigma 1 (k * (k * (n - 1) - 1)) = (k + 1) * (k * (n - 1)) := by
    rw [sigma_one_mul_coprime k (k * (n - 1) - 1) h_cop]
    rw [h_sigma_k, h_sigma_p]
  have h_rat_div : (sigma 1 (k * (k * (n - 1) - 1)) : ℤ) /. (k * (k * (n - 1) - 1) : ℤ) = ((k + 1) * (n - 1) : ℤ) /. (k * (n - 1) - 1 : ℤ) := by
    have h_num_eq : (sigma 1 (k * (k * (n - 1) - 1)) : ℤ) = ((k + 1) * (n - 1) : ℤ) * k := by
      rw [h_sigma_mul]
      push_cast
      ring
    have h_den_eq : (k * (k * (n - 1) - 1) : ℤ) = (k * (n - 1) - 1 : ℤ) * k := by
      push_cast
      ring
    rw [h_num_eq, h_den_eq]
    exact Rat.divInt_mul_right (by omega : (k : ℤ) ≠ 0)
  have h_div_eq_goal := nat_div_eq_divInt (sigma 1 (k * (k * (n - 1) - 1))) (k * (k * (n - 1) - 1))
  rw [h_div_eq_goal]
  rw [h_rat_div]
  have h_cop_num_den : Coprime ((k + 1) * (n - 1)) (k * (n - 1) - 1) := by
    -- We need to prove this coprime
    sorry
  have h_den_pos' : 0 < k * (n - 1) - 1 := h_p_pos
  have h_num_den := coprime_num_den ((k + 1) * (n - 1)) (k * (n - 1) - 1) h_den_pos' h_cop_num_den
  rw [h_num_den.1, h_num_den.2]
  push_cast
  omega
