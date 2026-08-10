import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

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

import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

theorem coprime_three_n_minus_one_two_n_minus_three (n : ℕ) (hn : 3 < n) (hp : (2 * n - 3).Prime) :
    Coprime (3 * (n - 1)) (2 * n - 3) := by
  have h_gcd_dvd_left : gcd (3 * (n - 1)) (2 * n - 3) ∣ 3 * (n - 1) := gcd_dvd_left _ _
  have h_gcd_dvd_right : gcd (3 * (n - 1)) (2 * n - 3) ∣ (2 * n - 3) := gcd_dvd_right _ _
  have h_dvd_mul_left : gcd (3 * (n - 1)) (2 * n - 3) ∣ 2 * (3 * (n - 1)) := dvd_mul_of_dvd_right h_gcd_dvd_left _
  have h_dvd_mul_right : gcd (3 * (n - 1)) (2 * n - 3) ∣ 3 * (2 * n - 3) := dvd_mul_of_dvd_right h_gcd_dvd_right _
  have h_sub : 2 * (3 * (n - 1)) - 3 * (2 * n - 3) = 3 := by omega
  have h_gcd_dvd_three : gcd (3 * (n - 1)) (2 * n - 3) ∣ 3 := by
    rw [← h_sub]
    exact Nat.dvd_sub' h_dvd_mul_left h_dvd_mul_right
  have h_prime_three : (3 : ℕ).Prime := prime_three
  rcases (Nat.dvd_prime h_prime_three).mp h_gcd_dvd_three with h_one | h_three
  · exact h_one
  · have h_three_dvd : 3 ∣ 2 * n - 3 := by
      rw [← h_three]
      exact h_gcd_dvd_right
    have h_prime_two_n_three : (2 * n - 3).Prime := hp
    rcases (Nat.dvd_prime h_prime_two_n_three).mp h_three_dvd with h_three_one | h_three_eq
    · contradiction
    · have : 2 * n - 3 > 3 := by omega
      omega





