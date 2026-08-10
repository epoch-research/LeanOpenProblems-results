import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 5000000
set_option maxRecDepth 2000000

def p : ℕ := 101702694862849

theorem h_div_zmod : (10 : ZMod p) ^ 4194304 = p - 1 := by
  unfold p
  reduce_mod_char

theorem h_div : p ∣ 10 ^ (2 ^ 22) + 1 := by
  have h_pow : 2 ^ 22 = 4194304 := rfl
  rw [h_pow]
  rw [← CharP.cast_eq_zero_iff (ZMod p) p]
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
  rw [h_div_zmod]
  unfold p
  reduce_mod_char

theorem not_prime_of_dvd (N d : ℕ) (h_div : d ∣ N) (h1 : 1 < d) (h2 : d < N) : ¬ Nat.Prime N := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd d h_div with hp1 | hp2
  · rw [hp1] at h1
    exact Nat.lt_irrefl 1 h1
  · rw [hp2] at h2
    exact Nat.lt_irrefl N h2

lemma bound_helper_22 (d n : ℕ) (hd : d < 10 ^ 15) (hn : 15 ≤ 2 ^ n) : d < 10 ^ (2 ^ n) + 1 := by
  have h_le : 10 ^ 15 ≤ 10 ^ (2 ^ n) + 1 := by
    have h_le_pow : 10 ^ 15 ≤ 10 ^ (2 ^ n) := Nat.pow_le_pow_right (by decide) hn
    exact Nat.le_add_right_of_le h_le_pow
  exact Nat.lt_of_lt_of_le hd h_le

theorem not_prime_10_2_22 : ¬ Nat.Prime (10 ^ (2 ^ 22) + 1) := by
  exact not_prime_of_dvd _ p h_div (by decide) (bound_helper_22 _ 22 (by decide) (by decide))
