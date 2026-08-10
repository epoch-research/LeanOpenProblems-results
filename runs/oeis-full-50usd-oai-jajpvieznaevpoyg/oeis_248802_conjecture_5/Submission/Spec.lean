import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000

/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

lemma nat_pow_eq_of_mod_eq (m a : ℕ) {x y T : ℕ}
    (hper : a ^ T ≡ 1 [MOD m]) (hxy : x % T = y % T) :
    a ^ x ≡ a ^ y [MOD m] := by
  rw [← Nat.div_add_mod x T, ← Nat.div_add_mod y T]
  rw [pow_add, pow_add, pow_mul, pow_mul]
  apply Nat.ModEq.mul
  · have hx1 : (a ^ T) ^ (x / T) ≡ 1 [MOD m] := by
      simpa using Nat.ModEq.pow (x / T) hper
    have hy1 : (a ^ T) ^ (y / T) ≡ 1 [MOD m] := by
      simpa using Nat.ModEq.pow (y / T) hper
    exact hx1.trans hy1.symm
  · rw [hxy]

lemma counterexample_divisibility :
    1399 ∣ (2 ^ (2 ^ (138 * 51 + 6) + 2) + 3) := by
  apply Nat.modEq_zero_iff_dvd.mp
  have hper : 2 ^ 1398 ≡ 1 [MOD 1399] := by
    exact Nat.ModEq.pow_card_sub_one_eq_one (by norm_num) (by norm_num)
  have hpow : 2 ^ (2 ^ (138 * 51 + 6) + 2) ≡ 2 ^ 672 [MOD 1399] := by
    apply nat_pow_eq_of_mod_eq 1399 2 hper
    decide
  have hsmall : 2 ^ 672 + 3 ≡ 0 [MOD 1399] := by decide
  exact (hpow.add (Nat.ModEq.refl 3)).trans hsmall

/--
Conjecture 5: a(138n+6) = 1669 for n >= 0 and n <> 2 mod 5.
-/
theorem oeis_248802_conjecture_5.disproof :
    ¬ (∀ (n : ℕ), n % 5 ≠ 2 → a (138 * n + 6) = 1669) := by
  intro h
  have ha := h 51 (by norm_num : 51 % 5 ≠ 2)
  unfold a at ha
  change Nat.minFac (2 ^ (2 ^ (138 * 51 + 6) + 2) + 3) = 1669 at ha
  have hle : Nat.minFac (2 ^ (2 ^ (138 * 51 + 6) + 2) + 3) ≤ 1399 :=
    Nat.minFac_le_of_dvd (by norm_num) counterexample_divisibility
  omega
