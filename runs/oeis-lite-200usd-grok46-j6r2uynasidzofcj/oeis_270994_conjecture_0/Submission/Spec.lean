import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

/-- If `2` has period `48` in `ZMod p`, then powers of two reduce modulo `48`. -/
private lemma two_pow_mod_period {p : ℕ} [NeZero p] (h : (2 : ZMod p) ^ 48 = 1) (n : ℕ) :
    (2 : ZMod p) ^ n = 2 ^ (n % 48) := by
  conv_lhs => rw [← Nat.div_add_mod n 48]
  rw [pow_add, pow_mul, h, one_pow, one_mul]

/-- A covering congruence at residue `n % 48` lifts to a divisibility for every `n`. -/
private lemma cover_dvd {p k n : ℕ} [NeZero p]
    (hper : (2 : ZMod p) ^ 48 = 1)
    (hcov : (k : ZMod p) * 2 ^ (n % 48) + 1 = 0) :
    p ∣ k * 2 ^ n + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [two_pow_mod_period hper]
  exact hcov

/-- The explicit Sierpiński number lying strictly between `a 473165` and `a 473165 + 28`. -/
private def kS : ℕ := 5292270077783

/-- `kS * 2^n + 1` is never prime, by a covering set of period 48. -/
private lemma kS_pow_not_prime (n : ℕ) (hn : 0 < n) :
    ¬ Nat.Prime (kS * 2 ^ n + 1) := by
  have hN : 673 < kS * 2 ^ n + 1 := by
    have h1 : 673 < kS * 2 + 1 := by decide
    have h2 : kS * 2 ≤ kS * 2 ^ n :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2) hn)
    omega
  have : n % 48 < 48 := Nat.mod_lt n (by decide)
  interval_cases hmod : n % 48
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 7) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 257) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 17) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 7) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 17) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 257) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 7) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 97) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 17) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 7) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 17) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 673) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 3) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)
  · exact Nat.not_prime_of_dvd_of_lt (cover_dvd (p := 5) (by decide) (by rw [hmod]; decide)) (by decide) (lt_of_le_of_lt (by decide) hN)

/-- `kS` is a Sierpiński number. -/
private lemma is_sierpinski_kS : is_sierpinski_number kS := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · intro n hn
    exact kS_pow_not_prime n hn

/--
oeis_270994_conjecture_0 is false: `a(n)` and `a(n)+28` are not always
consecutive Sierpiński numbers.  For `n = 473165`, the number
`a(n)+4 = 5292270077783` is itself a Sierpiński number (it admits the
covering set `{3, 5, 7, 17, 97, 257, 673}` of period 48).
-/
theorem oeis_270994_conjecture_0.disproof :
    ¬ (∀ n : ℕ,
      is_sierpinski_number (a n) ∧
      is_sierpinski_number (a n + 28) ∧
      (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  apply (h 473165).2.2 kS is_sierpinski_kS
  · -- a 473165 < kS
    simp [a, kS]
  · -- kS < a 473165 + 28
    simp [a, kS]

