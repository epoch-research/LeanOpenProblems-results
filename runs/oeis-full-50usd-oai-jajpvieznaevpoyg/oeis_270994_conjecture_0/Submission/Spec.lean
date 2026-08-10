import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

/--
A proper divisor of a natural number certifies that it is not prime.
-/
private lemma not_prime_of_dvd_lt {x p : ℕ} (hp2 : 2 ≤ p) (hd : p ∣ x) (hpx : p < x) :
    ¬ Nat.Prime x := by
  intro hx
  rcases hx.eq_one_or_self_of_dvd p hd with h | h
  · omega
  · omega


/-- A kernel-safe way to prove concrete equalities in `ZMod` by reducing natural remainders. -/
private lemma zmod_natCast_eq_of_mod_eq (a b n : ℕ) (h : a % n = b % n) :
    ((a : ℕ) : ZMod n) = ((b : ℕ) : ZMod n) := by
  exact (ZMod.natCast_eq_natCast_iff' a b n).2 h

/--
oeis_270994_conjecture_0: Are a(n) and a(n) + 28 always consecutive Sierpiński numbers?

This conjecture asserts that for all $n$, $a(n)$ and $a(n)+28$ are Sierpiński numbers,
and there are no Sierpiński numbers strictly between them.
-/
theorem oeis_270994_conjecture_0.disproof : ¬ ∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False) := by
  intro h
  have hk : is_sierpinski_number (a 602191 + 4) := by
    unfold is_sierpinski_number
    constructor
    · unfold a
      norm_num
    constructor
    · unfold a
      norm_num
    · intro m hm
      have hcover :
          m % 2 = 0 ∨ m % 4 = 3 ∨ m % 3 = 1 ∨ m % 8 = 1 ∨
          m % 16 = 13 ∨ m % 48 = 21 ∨ m % 48 = 5 := by
        omega
      have hbig (p : ℕ) (hp : p ≤ 673) : p < (a 602191 + 4) * 2^m + 1 := by
        have hpowpos : 0 < 2^m := pow_pos (by norm_num) m
        have hpow : 1 ≤ 2^m := by omega
        unfold a
        nlinarith
      rcases hcover with h2 | h5 | h7 | h17 | h257 | h97 | h673
      · have hdvd : 3 ∣ ((a 602191 + 4) * 2^m + 1) := by
          rw [← ZMod.natCast_eq_zero_iff ((a 602191 + 4) * 2^m + 1) 3]
          have hm' : m = 2 * (m / 2) + 0 := by omega
          rw [hm']
          simp only [pow_add, pow_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          have hpow : ((2 : ZMod 3) ^ 2) = 1 := by
            change ((4 : ℕ) : ZMod 3) = ((1 : ℕ) : ZMod 3)
            exact zmod_natCast_eq_of_mod_eq 4 1 3 (by norm_num)
          rw [hpow, one_pow]
          change ((6735401372844 : ℕ) : ZMod 3) = ((0 : ℕ) : ZMod 3)
          exact zmod_natCast_eq_of_mod_eq 6735401372844 0 3 (by norm_num)
        exact not_prime_of_dvd_lt (by norm_num) hdvd (hbig 3 (by norm_num))
      · have hdvd : 5 ∣ ((a 602191 + 4) * 2^m + 1) := by
          rw [← ZMod.natCast_eq_zero_iff ((a 602191 + 4) * 2^m + 1) 5]
          have hm' : m = 4 * (m / 4) + 3 := by omega
          rw [hm']
          simp only [pow_add, pow_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          have hpow : ((2 : ZMod 5) ^ 4) = 1 := by
            change ((16 : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5)
            exact zmod_natCast_eq_of_mod_eq 16 1 5 (by norm_num)
          rw [hpow, one_pow]
          change ((53883210982745 : ℕ) : ZMod 5) = ((0 : ℕ) : ZMod 5)
          exact zmod_natCast_eq_of_mod_eq 53883210982745 0 5 (by norm_num)
        exact not_prime_of_dvd_lt (by norm_num) hdvd (hbig 5 (by norm_num))
      · have hdvd : 7 ∣ ((a 602191 + 4) * 2^m + 1) := by
          rw [← ZMod.natCast_eq_zero_iff ((a 602191 + 4) * 2^m + 1) 7]
          have hm' : m = 3 * (m / 3) + 1 := by omega
          rw [hm']
          simp only [pow_add, pow_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          have hpow : ((2 : ZMod 7) ^ 3) = 1 := by
            change ((8 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
            exact zmod_natCast_eq_of_mod_eq 8 1 7 (by norm_num)
          rw [hpow, one_pow]
          change ((13470802745687 : ℕ) : ZMod 7) = ((0 : ℕ) : ZMod 7)
          exact zmod_natCast_eq_of_mod_eq 13470802745687 0 7 (by norm_num)
        exact not_prime_of_dvd_lt (by norm_num) hdvd (hbig 7 (by norm_num))
      · have hdvd : 17 ∣ ((a 602191 + 4) * 2^m + 1) := by
          rw [← ZMod.natCast_eq_zero_iff ((a 602191 + 4) * 2^m + 1) 17]
          have hm' : m = 8 * (m / 8) + 1 := by omega
          rw [hm']
          simp only [pow_add, pow_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          have hpow : ((2 : ZMod 17) ^ 8) = 1 := by
            change ((256 : ℕ) : ZMod 17) = ((1 : ℕ) : ZMod 17)
            exact zmod_natCast_eq_of_mod_eq 256 1 17 (by norm_num)
          rw [hpow, one_pow]
          change ((13470802745687 : ℕ) : ZMod 17) = ((0 : ℕ) : ZMod 17)
          exact zmod_natCast_eq_of_mod_eq 13470802745687 0 17 (by norm_num)
        exact not_prime_of_dvd_lt (by norm_num) hdvd (hbig 17 (by norm_num))
      · have hdvd : 257 ∣ ((a 602191 + 4) * 2^m + 1) := by
          rw [← ZMod.natCast_eq_zero_iff ((a 602191 + 4) * 2^m + 1) 257]
          have hm' : m = 16 * (m / 16) + 13 := by omega
          rw [hm']
          simp only [pow_add, pow_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          have hpow : ((2 : ZMod 257) ^ 16) = 1 := by
            change ((65536 : ℕ) : ZMod 257) = ((1 : ℕ) : ZMod 257)
            exact zmod_natCast_eq_of_mod_eq 65536 1 257 (by norm_num)
          rw [hpow, one_pow]
          change ((55176408046329857 : ℕ) : ZMod 257) = ((0 : ℕ) : ZMod 257)
          exact zmod_natCast_eq_of_mod_eq 55176408046329857 0 257 (by norm_num)
        exact not_prime_of_dvd_lt (by norm_num) hdvd (hbig 257 (by norm_num))
      · have hdvd : 97 ∣ ((a 602191 + 4) * 2^m + 1) := by
          rw [← ZMod.natCast_eq_zero_iff ((a 602191 + 4) * 2^m + 1) 97]
          have hm' : m = 48 * (m / 48) + 21 := by omega
          rw [hm']
          simp only [pow_add, pow_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          have hpow : ((2 : ZMod 97) ^ 48) = 1 := by
            change ((281474976710656 : ℕ) : ZMod 97) = ((1 : ℕ) : ZMod 97)
            exact zmod_natCast_eq_of_mod_eq 281474976710656 1 97 (by norm_num)
          rw [hpow, one_pow]
          change ((14125160459860443137 : ℕ) : ZMod 97) = ((0 : ℕ) : ZMod 97)
          exact zmod_natCast_eq_of_mod_eq 14125160459860443137 0 97 (by norm_num)
        exact not_prime_of_dvd_lt (by norm_num) hdvd (hbig 97 (by norm_num))
      · have hdvd : 673 ∣ ((a 602191 + 4) * 2^m + 1) := by
          rw [← ZMod.natCast_eq_zero_iff ((a 602191 + 4) * 2^m + 1) 673]
          have hm' : m = 48 * (m / 48) + 5 := by omega
          rw [hm']
          simp only [pow_add, pow_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
          have hpow : ((2 : ZMod 673) ^ 48) = 1 := by
            change ((281474976710656 : ℕ) : ZMod 673) = ((1 : ℕ) : ZMod 673)
            exact zmod_natCast_eq_of_mod_eq 281474976710656 1 673 (by norm_num)
          rw [hpow, one_pow]
          change ((215532843930977 : ℕ) : ZMod 673) = ((0 : ℕ) : ZMod 673)
          exact zmod_natCast_eq_of_mod_eq 215532843930977 0 673 (by norm_num)
        exact not_prime_of_dvd_lt (by norm_num) hdvd (hbig 673 (by norm_num))
  exact (h 602191).2.2 (a 602191 + 4) hk (by omega) (by omega)
