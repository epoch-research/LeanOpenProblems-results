import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000


/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

lemma pow_eq_of_mod_eq {M : Type} [Monoid M] (a : M) {x y T : ℕ}
    (hper : a ^ T = 1) (hxy : x % T = y % T) : a ^ x = a ^ y := by
  rw [← Nat.div_add_mod x T, ← Nat.div_add_mod y T]
  rw [pow_add, pow_add, pow_mul, pow_mul, hper, one_pow, one_pow, one_mul, one_mul, hxy]

lemma zmod_pow_reduce_prime (p x y : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hxy : x % (p-1) = y % (p-1)) :
    (2 : ZMod p)^x = (2 : ZMod p)^y := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (le_antisymm hple hp.two_le)
  exact pow_eq_of_mod_eq (2 : ZMod p) (ZMod.pow_card_sub_one_eq_one h2ne) hxy

lemma counterexample_divisibility :
    1399 ∣ (2 ^ (2 ^ (138 * 51 + 6) + 2) + 3) := by
  rw [← ZMod.natCast_eq_zero_iff (2 ^ (2 ^ (138 * 51 + 6) + 2) + 3) 1399]
  have hred : (2 : ZMod 1399) ^ (2 ^ (138 * 51 + 6) + 2) = (2 : ZMod 1399) ^ 672 := by
    apply zmod_pow_reduce_prime 1399 _ _ (by norm_num) (by norm_num)
    native_decide
  change (2 : ZMod 1399) ^ (2 ^ (138 * 51 + 6) + 2) + 3 = 0
  rw [hred]
  native_decide

/--
Conjecture 5: a(138n+6) = 1669 for n >= 0 and n <> 2 mod 5.
-/
theorem oeis_248802_conjecture_5.disproof :
    ¬ (∀ (n : ℕ), n % 5 ≠ 2 → a (138 * n + 6) = 1669) := by
  intro h
  have h51 : 51 % 5 ≠ 2 := by norm_num
  have ha := h 51 h51
  unfold a at ha
  have hle : Nat.minFac (2 ^ (2 ^ (138 * 51 + 6) + 2) + 3) ≤ 1399 :=
    Nat.minFac_le_of_dvd (by norm_num) counterexample_divisibility
  omega
