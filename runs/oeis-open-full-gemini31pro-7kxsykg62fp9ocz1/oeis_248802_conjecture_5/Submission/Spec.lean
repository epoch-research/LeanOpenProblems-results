import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option exponentiation.threshold 8000

/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

/--
Conjecture 5: a(138n+6) = 1669 for n >= 0 and n <> 2 mod 5.
-/
theorem oeis_248802_conjecture_5 (n : ℕ) (h : n % 5 ≠ 2) : a (138 * n + 6) = 1669 := by
  sorry

lemma h1 : ∃ k : ℕ, 2 ^ 7044 + 2 = 1398 * k + 672 := by
  use (2 ^ 7044) / 1398
  have : (2 ^ 7044) % 1398 = 670 := by decide
  calc 2 ^ 7044 + 2
    _ = 1398 * ((2 ^ 7044) / 1398) + (2 ^ 7044) % 1398 + 2 := by rw [Nat.div_add_mod (2 ^ 7044) 1398]
    _ = 1398 * ((2 ^ 7044) / 1398) + 670 + 2 := by rw [this]
    _ = 1398 * ((2 ^ 7044) / 1398) + 672 := by omega

lemma h2 (k : ℕ) : ((2 ^ (1398 * k + 672) + 3 : ℕ) : ZMod 1399) = 0 := by
  push_cast
  rw [pow_add, pow_mul]
  have : (2 : ZMod 1399) ^ 1398 = 1 := by decide
  rw [this, one_pow, one_mul]
  decide

lemma h4 : 1399 ∣ 2 ^ (2 ^ 7044 + 2) + 3 := by
  have H : ((2 ^ (2 ^ 7044 + 2) + 3 : ℕ) : ZMod 1399) = 0 := by
    rcases h1 with ⟨k, hk⟩
    rw [hk]
    exact h2 k
  exact (CharP.cast_eq_zero_iff (ZMod 1399) 1399 _).mp H

lemma h5 : a 7044 ≤ 1399 := by
  unfold a
  exact Nat.minFac_le_of_dvd (by decide) h4

lemma h6 : a 7044 ≠ 1669 := by
  intro contra
  have h := h5
  rw [contra] at h
  revert h
  decide

theorem oeis_248802_conjecture_5.disproof : ¬ (type_of% @oeis_248802_conjecture_5) := by
  intro H
  have h_eq := H 51 (by decide)
  have h_7044 : 138 * 51 + 6 = 7044 := by decide
  rw [h_7044] at h_eq
  exact h6 h_eq
