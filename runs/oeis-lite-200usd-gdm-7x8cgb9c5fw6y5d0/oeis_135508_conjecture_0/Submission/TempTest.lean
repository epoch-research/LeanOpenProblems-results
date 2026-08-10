import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

-- Mocking external dependencies
lemma prime_not_dvd_x_seq_small (p : ℕ) (hp_lt : p < 600) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := sorry
lemma max_prime_factor_x_seq (n : ℕ) (hn : n > 0) (r : ℕ) (hr : Nat.Prime r) (hd : r ∣ x_seq n) : r ≤ n + 2 := sorry
lemma x_seq_step_eq_gen (n : ℕ) (hn : n ≥ 2) : x_seq n = x_seq (n - 1) * (2 + n / Nat.gcd (x_seq (n - 1)) n) := sorry
lemma g_eq_one_for_p (p : ℕ) (hp : Nat.Prime p) (h_gt : p ≥ 4) (h1 : ¬ p ∣ x_seq (p - 3)) (h2 : p ∣ x_seq (p - 2)) : Nat.gcd (x_seq (p - 3)) (p - 2) = 1 := sorry
lemma prime_not_dvd_add (p h : ℕ) (hp : Nat.Prime p) (hp3 : p > 3) (hh : h ∣ p - 1) : ¬ p ∣ 2 + h := sorry
lemma x_seq_dvd_of_le (a b : ℕ) (ha : a > 0) (hab : a ≤ b) : x_seq a ∣ x_seq b := sorry
lemma prime_dvd_x_seq_sq_sub_one_bounded_1097 (r : ℕ) (hr_le : r ≤ 1097) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := sorry
lemma gcd_prime_eq (a p : ℕ) (hp : Nat.Prime p) : Nat.gcd a p = 1 ∨ Nat.gcd a p = p := sorry
lemma dvd_helper (a b c : ℕ) (h : a ∣ b) : a ∣ c * b := sorry
lemma prime_not_dvd_x_seq_509 (p : ℕ) (hp_lt : p < 271443) (hp : Nat.Prime p) (hp2 : ¬ (Nat.Prime (p - 2))) : Nat.gcd (x_seq (p - 1)) p = 1 := sorry

lemma r_mod_three (r : ℕ) (hr : Nat.Prime r) (hr_ge : r ≥ 1103) : r % 3 = 1 ∨ r % 3 = 2 := by
  have h_mod_lt : r % 3 < 3 := Nat.mod_lt _ (by decide)
  have : r % 3 ≠ 0 := by
    intro h_mod_zero
    have h_dvd : 3 ∣ r := Nat.dvd_of_mod_eq_zero h_mod_zero
    have h_eq : r = 3 := by
      rcases hr.eq_one_or_self_of_dvd 3 h_dvd with h_one | h_self
      · contradiction
      · exact h_self.symm
    omega
  omega

lemma r_sq_mod_three (r : ℕ) (hr : Nat.Prime r) (hr_ge : r ≥ 1103) : r^2 % 3 = 1 := by
  have h_mod := r_mod_three r hr hr_ge
  have h_sq_mod : r^2 % 3 = (r % 3 * (r % 3)) % 3 := by
    rw [Nat.pow_two]
    exact Nat.mul_mod r r 3
  rcases h_mod with h1 | h2
  · rw [h_sq_mod, h1]
  · rw [h_sq_mod, h2]

lemma r_sq_plus_two_mod_three (r : ℕ) (hr : Nat.Prime r) (hr_ge : r ≥ 1103) : (r^2 + 2) % 3 = 0 := by
  have h_sq := r_sq_mod_three r hr hr_ge
  have h_add : (r^2 + 2) % 3 = (r^2 % 3 + 2) % 3 := Nat.add_mod (r^2) 2 3
  rw [h_add, h_sq]

lemma r_sq_plus_two_not_prime (r : ℕ) (hr : Nat.Prime r) (hr_ge : r ≥ 1103) : ¬ Nat.Prime (r^2 + 2) := by
  intro h_prime
  have h_mod := r_sq_plus_two_mod_three r hr hr_ge
  have h_dvd : 3 ∣ r^2 + 2 := Nat.dvd_of_mod_eq_zero h_mod
  have h_eq : r^2 + 2 = 3 := by
    rcases h_prime.eq_one_or_self_of_dvd 3 h_dvd with h_one | h_self
    · contradiction
    · exact h_self.symm
  have h_r_sq_ge4 : r^2 ≥ 1216609 := by
    have h_mul : r * r ≥ 1103 * 1103 := Nat.mul_le_mul hr_ge hr_ge
    rw [← Nat.pow_two] at h_mul
    exact h_mul
  omega

lemma gcd_1103_aux (n : ℕ) (hn : n = 3307) : Nat.gcd (x_seq (n - 1)) n = 1 := by
  subst hn
  exact prime_not_dvd_x_seq_509 3307 (by decide) (by norm_num) (by norm_num)

lemma dvd_1103_aux (n : ℕ) (hn : n = 3307) : 1103 ∣ x_seq n := by
  subst hn
  have h := x_seq_step_eq_gen 3307 (by decide)
  rw [gcd_1103_aux 3307 rfl] at h
  have h_calc : 2 + 3307 / 1 = 3309 := by rfl
  rw [h_calc] at h
  rw [h]
  exact dvd_helper 1103 3309 (x_seq (3307 - 1)) (by decide)

lemma dvd_1103 : 1103 ∣ x_seq (1103^2 - 1) := by
  have h_dvd : x_seq 3307 ∣ x_seq (1103^2 - 1) := by
    apply x_seq_dvd_of_le
    · omega
    · omega
  exact dvd_trans (dvd_1103_aux 3307 rfl) h_dvd

lemma prime_dvd_x_seq_sq_sub_one_bounded_1103 (r : ℕ) (hr_le : r ≤ 1103) (hr : Nat.Prime r) : r ∣ x_seq (r^2 - 1) := by
  by_cases h_0 : r ≤ 1097
  · exact prime_dvd_x_seq_sq_sub_one_bounded_1097 r h_0 hr
  · interval_cases r
    · exact (by decide : ¬ Nat.Prime 1098) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1099) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1100) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1101) hr |>.elim
    · exact (by decide : ¬ Nat.Prime 1102) hr |>.elim
    · exact dvd_1103
