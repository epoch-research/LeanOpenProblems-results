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

theorem nat_dvd_sub {a b c : ℕ} (h : c ≤ b) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := by
  rcases h1 with ⟨x, rfl⟩
  rcases h2 with ⟨y, rfl⟩
  use x - y
  rw [← Nat.mul_sub_left_distrib]

theorem sigma_one_mul_coprime (a b : ℕ) (h : Coprime a b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b := by
  exact isMultiplicative_sigma.map_mul_of_coprime h

theorem coprime_three_n_minus_one_two_n_minus_three (n : ℕ) (hn : 3 < n) (hp : (2 * n - 3).Prime) :
    Coprime (3 * (n - 1)) (2 * n - 3) := by
  have h_gcd_dvd_left : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ 3 * (n - 1) := Nat.gcd_dvd_left _ _
  have h_gcd_dvd_right : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ (2 * n - 3) := Nat.gcd_dvd_right _ _
  have h_dvd_mul_left : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ 2 * (3 * (n - 1)) := dvd_mul_of_dvd_right h_gcd_dvd_left _
  have h_dvd_mul_right : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ 3 * (2 * n - 3) := dvd_mul_of_dvd_right h_gcd_dvd_right _
  have h_le : 3 * (2 * n - 3) ≤ 2 * (3 * (n - 1)) := by omega
  have h_sub : 2 * (3 * (n - 1)) - 3 * (2 * n - 3) = 3 := by omega
  have h_gcd_dvd_sub : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ 2 * (3 * (n - 1)) - 3 * (2 * n - 3) :=
    nat_dvd_sub h_le h_dvd_mul_left h_dvd_mul_right
  have h_gcd_dvd_three : Nat.gcd (3 * (n - 1)) (2 * n - 3) ∣ 3 := by
    rwa [h_sub] at h_gcd_dvd_sub
  have h_prime_three : (3 : ℕ).Prime := prime_three
  rcases (Nat.dvd_prime h_prime_three).mp h_gcd_dvd_three with h_one | h_three
  · exact h_one
  · have h_three_dvd : 3 ∣ 2 * n - 3 := by
      rw [h_three] at h_gcd_dvd_right
      exact h_gcd_dvd_right
    have h_prime_two_n_three : (2 * n - 3).Prime := hp
    rcases (Nat.dvd_prime h_prime_two_n_three).mp h_three_dvd with h_three_one | h_three_eq
    · contradiction
    · have : 2 * n - 3 > 3 := by omega
      omega

theorem prime_two_case (n : ℕ) (hn : 3 < n) (hp : (2 * n - 3).Prime) :
    A243473_val (2 * (2 * n - 3)) = n := by
  unfold A243473_val
  have h_two_ne : (2 : ℕ) ≠ 0 := by decide
  have h_prime_two_n_three : (2 * n - 3).Prime := hp
  have h_prime_ne_zero : (2 * n - 3) ≠ 0 := by
    exact Nat.ne_of_gt (Nat.Prime.pos hp)
  have hi_ne_zero : 2 * (2 * n - 3) ≠ 0 := Nat.mul_ne_zero h_two_ne h_prime_ne_zero
  rw [if_neg hi_ne_zero]
  have h_cop_two : Coprime 2 (2 * n - 3) := by
    have h_prime_two_n_three_gt_two : 2 < 2 * n - 3 := by omega
    have h_cop : Coprime (2 * n - 3) 2 := by
      exact Nat.Prime.coprime_iff_not_dvd hp |>.mpr (fun hd => by
        have : 2 * n - 3 ∣ 2 := hd
        have := Nat.le_of_dvd (by decide) this
        omega)
    exact h_cop.symm
  have h_sigma_two : sigma 1 2 = 3 := by rfl
  have h_sigma_prime : sigma 1 (2 * n - 3) = 2 * n - 2 := by
    rw [sigma_apply, Nat.Prime.divisors hp]
    have h_ne : 1 ≠ 2 * n - 3 := by omega
    have h_not_mem : 1 ∉ ({2 * n - 3} : Finset ℕ) := by
      simp; omega
    rw [Finset.sum_insert h_not_mem]
    simp
    omega
  have h_sigma_mul : sigma 1 (2 * (2 * n - 3)) = 6 * (n - 1) := by
    rw [sigma_one_mul_coprime 2 (2 * n - 3) h_cop_two]
    rw [h_sigma_two, h_sigma_prime]
    omega
  have h_le_n : 1 ≤ n := by omega
  have h_le_2n : 3 ≤ 2 * n := by omega
  have h_rat_div : (sigma 1 (2 * (2 * n - 3)) : ℤ) /. (2 * (2 * n - 3) : ℤ) = (3 * (n - 1) : ℤ) /. (2 * n - 3 : ℤ) := by
    have h_num_eq : (sigma 1 (2 * (2 * n - 3)) : ℤ) = (3 * (n - 1) : ℤ) * 2 := by
      rw [h_sigma_mul]
      push_cast [h_le_n]
      ring
    have h_den_eq : (2 * (2 * n - 3) : ℤ) = (2 * n - 3 : ℤ) * 2 := by
      push_cast [h_le_2n]
      ring
    rw [h_num_eq, h_den_eq]
    exact Rat.divInt_mul_right (by decide : (2 : ℤ) ≠ 0)
  have h_div_eq_goal := nat_div_eq_divInt (sigma 1 (2 * (2 * n - 3))) (2 * (2 * n - 3))
  rw [h_div_eq_goal]
  push_cast [h_le_n, h_le_2n]
  rw [h_rat_div]
  have h_cop_three_n : Coprime (3 * (n - 1)) (2 * n - 3) := coprime_three_n_minus_one_two_n_minus_three n hn hp

  have h_den_pos : 0 < 2 * n - 3 := by omega
  have h_num_den := coprime_num_den (3 * (n - 1)) (2 * n - 3) h_den_pos h_cop_three_n
  push_cast [h_le_n, h_le_2n] at h_num_den
  rw [h_num_den.1, h_num_den.2]
  push_cast [h_le_n, h_le_2n]
  omega







