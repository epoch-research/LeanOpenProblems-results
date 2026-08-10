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

theorem nat_dvd_sub {a b c : ℕ} (h : c ≤ b) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := by
  rcases h1 with ⟨x, rfl⟩
  rcases h2 with ⟨y, rfl⟩
  use x - y
  rw [← Nat.mul_sub_left_distrib]

theorem coprime_mul_sub_one (k A : ℕ) (h : 0 < k * A) : Coprime A (k * A - 1) := by
  apply Nat.coprime_of_dvd
  intro d hd1 hd2 hd3
  have hd4 : d ∣ k * A := dvd_mul_of_dvd_right hd2 k
  have h_le : k * A - 1 ≤ k * A := by omega
  have hd5 : d ∣ k * A - (k * A - 1) := nat_dvd_sub h_le hd4 hd3
  have h_sub : k * A - (k * A - 1) = 1 := by omega
  rw [h_sub] at hd5
  have hd6 : d ≤ 1 := Nat.le_of_dvd (by decide) hd5
  have : d > 1 := hd1.one_lt
  omega

theorem coprime_helper_left (n k : ℕ) (hk : Coprime (k + 1) n) (h_pos : 0 < k * (n - 1)) :
    Coprime (k + 1) (k * (n - 1) - 1) := by
  apply Nat.coprime_of_dvd
  intro d hd1 hd2 hd3
  have hd4 : d ∣ (k + 1) * (n - 1) := dvd_mul_of_dvd_left hd2 (n - 1)
  have h_eq : (k + 1) * (n - 1) = k * (n - 1) + (n - 1) := by ring
  rw [h_eq] at hd4
  have h_le : k * (n - 1) - 1 ≤ k * (n - 1) + (n - 1) := by omega
  have hd5 : d ∣ (k * (n - 1) + (n - 1)) - (k * (n - 1) - 1) := nat_dvd_sub h_le hd4 hd3
  have hn_gt : n - 1 ≥ 1 := by
    by_contra hc
    have : n - 1 = 0 := by omega
    have h_pos_rewrite := h_pos
    rw [this] at h_pos_rewrite
    simp at h_pos_rewrite
  have hn_eq : n = (n - 1) + 1 := by omega
  have h_sub : (k * (n - 1) + (n - 1)) - (k * (n - 1) - 1) = n := by omega
  rw [h_sub] at hd5
  have hd6 : d ∣ Nat.gcd (k + 1) n := Nat.dvd_gcd hd2 hd5
  have h_gcd_eq : Nat.gcd (k + 1) n = 1 := hk
  rw [h_gcd_eq] at hd6
  have hd7 : d ≤ 1 := Nat.le_of_dvd (by decide) hd6
  have : d > 1 := hd1.one_lt
  omega

theorem coprime_helper (n k : ℕ) (hk : Coprime (k + 1) n) (h_pos : 0 < k * (n - 1)) :
    Coprime ((k + 1) * (n - 1)) (k * (n - 1) - 1) := by
  have hc1 : Coprime (n - 1) (k * (n - 1) - 1) := coprime_mul_sub_one k (n - 1) h_pos
  have hc2 : Coprime (k + 1) (k * (n - 1) - 1) := coprime_helper_left n k hk h_pos
  exact Nat.Coprime.mul_left hc2 hc1

def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

theorem prime_k_case (n : ℕ) (k : ℕ) (hk : k.Prime) (hn : 2 < n) (hk_cop : Coprime (k + 1) n) (hp : (k * (n - 1) - 1).Prime) (h_cop : Coprime k (k * (n - 1) - 1)) :
    A243473_val (k * (k * (n - 1) - 1)) = n := by
  unfold A243473_val
  have hk_pos : 0 < k := hk.pos
  have h_p_pos : 0 < k * (n - 1) - 1 := hp.pos
  have hi_ne_zero : k * (k * (n - 1) - 1) ≠ 0 := Nat.mul_ne_zero hk_pos.ne' h_p_pos.ne'
  rw [if_neg hi_ne_zero]
  have h_sigma_k : sigma 1 k = k + 1 := by
    rw [sigma_apply, Nat.Prime.divisors hk]
    have h_ne : 1 ≠ k := hk.ne_one.symm
    have h_not_mem : 1 ∉ ({k} : Finset ℕ) := by
      simp; exact h_ne
    rw [Finset.sum_insert h_not_mem]
    simp
  have h_sigma_p : sigma 1 (k * (n - 1) - 1) = k * (n - 1) := by
    rw [sigma_apply, Nat.Prime.divisors hp]
    have h_ne : 1 ≠ k * (n - 1) - 1 := by omega
    have h_not_mem : 1 ∉ ({k * (n - 1) - 1} : Finset ℕ) := by
      simp; exact h_ne
    rw [Finset.sum_insert h_not_mem]
    simp
    omega
  have h_sigma_mul : sigma 1 (k * (k * (n - 1) - 1)) = (k + 1) * (k * (n - 1)) := by
    rw [sigma_one_mul_coprime k (k * (n - 1) - 1) h_cop]
    rw [h_sigma_k, h_sigma_p]
  have h_le_n : 1 ≤ n := by omega
  have h_rat_div : (sigma 1 (k * (k * (n - 1) - 1)) : ℤ) /. (k * (k * (n - 1) - 1) : ℤ) = ((k + 1) * (n - 1) : ℤ) /. (k * (n - 1) - 1 : ℤ) := by
    have h_num_eq : (sigma 1 (k * (k * (n - 1) - 1)) : ℤ) = ((k + 1) * (n - 1) : ℤ) * k := by
      rw [h_sigma_mul]
      push_cast [h_le_n]
      ring
    have h_den_eq : (k * (k * (n - 1) - 1) : ℤ) = (k * (n - 1) - 1 : ℤ) * k := by
      push_cast [h_le_n]
      ring
    rw [h_num_eq, h_den_eq]
    exact Rat.divInt_mul_right (by omega : (k : ℤ) ≠ 0)
  have h_div_eq_goal := nat_div_eq_divInt (sigma 1 (k * (k * (n - 1) - 1))) (k * (k * (n - 1) - 1))
  rw [h_div_eq_goal]
  push_cast [h_le_n]
  rw [h_rat_div]
  have h_pos : 0 < k * (n - 1) := by
    have : 0 < n - 1 := by omega
    exact Nat.mul_pos hk_pos this
  have h_cop_num_den : Coprime ((k + 1) * (n - 1)) (k * (n - 1) - 1) := coprime_helper n k hk_cop h_pos
  have h_den_pos' : 0 < k * (n - 1) - 1 := h_p_pos
  have h_num_den := coprime_num_den ((k + 1) * (n - 1)) (k * (n - 1) - 1) h_den_pos' h_cop_num_den
  push_cast [h_le_n] at h_num_den
  rw [h_num_den.1, h_num_den.2]
  push_cast [h_le_n]
  omega
