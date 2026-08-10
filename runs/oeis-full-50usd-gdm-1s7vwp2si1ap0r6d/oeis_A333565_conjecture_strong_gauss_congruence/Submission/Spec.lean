import FormalConjectures.Util.ProblemImports

open Nat Int BigOperators

set_option linter.unusedVariables false

def A333565 (n : ℕ) : ℕ :=
  match n % 12 with
  | 0 => 1
  | 1 => 7
  | 2 => 33
  | 3 => 223
  | 4 => 1
  | 5 => 7
  | 6 => 33
  | 7 => 7
  | 8 => 1
  | 9 => 223
  | 10 => 33
  | _ => 7

lemma coprime_dvd_mul_pow (q p n : ℕ) (m : ℕ) (hq : Nat.Prime q) (hp : Nat.Prime p) (hqp : q ≠ p) :
    q ∣ n * p ^ m ↔ q ∣ n := by
  induction m with
  | zero =>
    rw [pow_zero, mul_one]
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, Nat.Prime.dvd_mul hq]
    have h_not_dvd : ¬ q ∣ p := by
      intro h
      have : q = p := ((Nat.Prime.dvd_iff_eq hp hq.ne_one).mp h).symm
      exact hqp this
    tauto

lemma helper_3 (n : ℕ) (hn : n > 0) : (A333565 (n * 3) : ℤ) ≡ (A333565 n : ℤ) [ZMOD 27] := by
  have h_mod : n % 12 = 0 ∨ n % 12 = 1 ∨ n % 12 = 2 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨ n % 12 = 5 ∨
               n % 12 = 6 ∨ n % 12 = 7 ∨ n % 12 = 8 ∨ n % 12 = 9 ∨ n % 12 = 10 ∨ n % 12 = 11 := by omega
  rcases h_mod with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals (unfold A333565)
  all_goals (have h_mod3 : (n * 3) % 12 = (n % 12 * 3) % 12 := by rw [mul_comm, Nat.mul_mod, mul_comm])
  all_goals (rw [h_mod3, h])
  all_goals (try decide)

lemma helper_3_large (n : ℕ) (k : ℕ) (hn : n > 0) (hk : k ≥ 2) :
    A333565 (n * 3 ^ k) = A333565 (n * 3 ^ (k - 1)) := by
  have hk1 : k ≥ 1 := by omega
  have hkm1 : k - 1 ≥ 1 := by omega
  have h_pow_3_div (m : ℕ) (hm : m ≥ 1) : 3 ∣ 3 ^ m := by
    have : m = (m - 1) + 1 := by omega
    rw [this, pow_succ]
    exact dvd_mul_left 3 (3 ^ (m - 1))
  have hdvd3 : 3 ∣ n * 3 ^ (k - 1) := dvd_mul_of_dvd_right (h_pow_3_div (k-1) hkm1) n
  have h_mod_3 : (n * 3 ^ (k - 1)) % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd3
  have h_mod_12 : (n * 3 ^ (k - 1)) % 12 = 0 ∨ (n * 3 ^ (k - 1)) % 12 = 3 ∨ (n * 3 ^ (k - 1)) % 12 = 6 ∨ (n * 3 ^ (k - 1)) % 12 = 9 := by
    have h_div : (n * 3 ^ (k - 1)) % 12 < 12 := Nat.mod_lt _ (by decide)
    have h_dvd : 3 ∣ (n * 3 ^ (k - 1)) % 12 := Nat.dvd_of_mod_eq_zero (by
      rw [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 12)]
      exact h_mod_3
    )
    omega
  have h_3x : n * 3 ^ k = (n * 3 ^ (k - 1)) * 3 := by
    nth_rw 1 [← Nat.sub_add_cancel hk1]
    rw [pow_succ, mul_assoc]
  rcases h_mod_12 with h | h | h | h
  · have h_mod_3x : (n * 3 ^ k) % 12 = ((n * 3 ^ (k - 1)) % 12 * 3) % 12 := by rw [h_3x, mul_comm, Nat.mul_mod, mul_comm]
    unfold A333565; rw [h, h_mod_3x, h]
  · have h_mod_3x : (n * 3 ^ k) % 12 = ((n * 3 ^ (k - 1)) % 12 * 3) % 12 := by rw [h_3x, mul_comm, Nat.mul_mod, mul_comm]
    unfold A333565; rw [h, h_mod_3x, h]
  · have h_mod_3x : (n * 3 ^ k) % 12 = ((n * 3 ^ (k - 1)) % 12 * 3) % 12 := by rw [h_3x, mul_comm, Nat.mul_mod, mul_comm]
    unfold A333565; rw [h, h_mod_3x, h]
  · have h_mod_3x : (n * 3 ^ k) % 12 = ((n * 3 ^ (k - 1)) % 12 * 3) % 12 := by rw [h_3x, mul_comm, Nat.mul_mod, mul_comm]
    unfold A333565; rw [h, h_mod_3x, h]

lemma helper_coprime (p n k : ℕ) (hp : Nat.Prime p) (hp_not_two : p ≠ 2) (hp_not_three : p ≠ 3) (hn : n > 0) (hk : k > 0) :
    A333565 (n * p ^ k) = A333565 (n * p ^ (k - 1)) := by
  have hp_mod_12 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by
    have h_lt : p % 12 < 12 := Nat.mod_lt _ (by decide)
    have hp_odd : p % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hp with rfl | h_odd
      · contradiction
      · exact h_odd
    have hp_not_div_3 : ¬ 3 ∣ p := by
      intro h
      have : p = 3 := (Nat.Prime.dvd_iff_eq hp (by decide)).mp h
      exact hp_not_three this
    have h_mod_2 : p % 2 = 1 := hp_odd
    have h_mod_3 : p % 3 = 1 ∨ p % 3 = 2 := by
      have : p % 3 < 3 := Nat.mod_lt _ (by decide)
      have : p % 3 ≠ 0 := by
        intro h
        apply hp_not_div_3
        exact Nat.dvd_of_mod_eq_zero h
      omega
    have h_mod_12_not_div_2 : ¬ 2 ∣ p % 12 := by
      intro h
      have hd12 : 2 ∣ 12 := by decide
      have : p = 2 := (Nat.Prime.dvd_iff_eq hp (by decide)).mp (by
        have : 2 ∣ p := by
          rw [← Nat.mod_add_div p 12]
          exact dvd_add h (dvd_mul_of_dvd_left hd12 (p / 12))
        exact this
      )
      exact hp_not_two this
    have h_mod_12_not_div_3 : ¬ 3 ∣ p % 12 := by
      intro h
      have hd12 : 3 ∣ 12 := by decide
      have : p = 3 := (Nat.Prime.dvd_iff_eq hp (by decide)).mp (by
        have : 3 ∣ p := by
          rw [← Nat.mod_add_div p 12]
          exact dvd_add h (dvd_mul_of_dvd_left hd12 (p / 12))
        exact this
      )
      exact hp_not_three this
    omega

  have h_px : n * p ^ k = (n * p ^ (k - 1)) * p := by
    have hk1 : k ≥ 1 := by omega
    nth_rw 1 [← Nat.sub_add_cancel hk1]
    rw [pow_succ, mul_assoc]

  have h_mod : (n * p ^ k) % 12 = ((n * p ^ (k - 1)) % 12 * (p % 12)) % 12 := by
    rw [h_px, mul_comm, Nat.mul_mod, mul_comm]

  have h_z_mod : (n * p ^ (k - 1)) % 12 = 0 ∨ (n * p ^ (k - 1)) % 12 = 1 ∨ (n * p ^ (k - 1)) % 12 = 2 ∨ (n * p ^ (k - 1)) % 12 = 3 ∨ (n * p ^ (k - 1)) % 12 = 4 ∨ (n * p ^ (k - 1)) % 12 = 5 ∨ (n * p ^ (k - 1)) % 12 = 6 ∨ (n * p ^ (k - 1)) % 12 = 7 ∨ (n * p ^ (k - 1)) % 12 = 8 ∨ (n * p ^ (k - 1)) % 12 = 9 ∨ (n * p ^ (k - 1)) % 12 = 10 ∨ (n * p ^ (k - 1)) % 12 = 11 := by omega
  rcases hp_mod_12 with hp12 | hp12 | hp12 | hp12
  all_goals {
    rcases h_z_mod with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals (unfold A333565)
    all_goals (rw [h, h_mod, h, hp12])
  }

theorem oeis_A333565_conjecture_strong_gauss_congruence (p n k : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) (hn : n > 0) (hk : k > 0) :
    (A333565 (n * p ^ k) : ℤ) ≡ (A333565 (n * p ^ (k - 1)) : ℤ) [ZMOD (↑p ^ (3 * k) : ℤ)] := by
  have hp_eq_3 : p = 3 ∨ p ≠ 3 := by omega
  rcases hp_eq_3 with rfl | hp_not_three
  · -- p = 3
    have hk1 : k = 1 ∨ k ≥ 2 := by omega
    rcases hk1 with rfl | hk2
    · -- k = 1
      have h_pow_1 : 3 ^ 1 = 3 := by rfl
      have h_pow_0 : 3 ^ (1 - 1) = 1 := by rfl
      rw [h_pow_1, h_pow_0]
      change (A333565 (n * 3) : ℤ) ≡ (A333565 (n * 1) : ℤ) [ZMOD 27]
      rw [mul_one]
      exact helper_3 n hn
    · -- k ≥ 2
      have heq : A333565 (n * 3 ^ k) = A333565 (n * 3 ^ (k - 1)) := helper_3_large n k hn hk2
      rw [heq]
  · -- p ≠ 3
    have hp_not_two : p ≠ 2 := by omega
    have heq : A333565 (n * p ^ k) = A333565 (n * p ^ (k - 1)) := helper_coprime p n k hp hp_not_two hp_not_three hn hk
    rw [heq]
