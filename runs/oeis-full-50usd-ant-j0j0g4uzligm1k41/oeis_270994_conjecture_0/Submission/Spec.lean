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
Disproof of `oeis_270994_conjecture_0`.

The conjecture claims that for every `n`, the numbers `a n` and `a n + 28` are Sierpiński
numbers with no Sierpiński number strictly between them.  This is false: for `n = 473165`
the number `K = a 473165 + 4 = 5292270077783` is itself a Sierpiński number lying strictly
between `a 473165` and `a 473165 + 28`.

Indeed, `K` admits the covering set `{3, 5, 7, 17, 97, 257, 673}`: every prime in it has
multiplicative order dividing `48` for the base `2`, and for every residue `r < 48` at least
one of these primes divides `K * 2 ^ r + 1`.  Consequently `K * 2 ^ m + 1` is divisible by one
of these (small) primes for every `m`, hence composite, so `K` is a Sierpiński number.
-/
theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  obtain ⟨_, _, hbetween⟩ := h 473165
  refine hbetween 5292270077783 ?_ ?_ ?_
  · -- `5292270077783` is a Sierpiński number.
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro m hm
    -- Covering set `{3, 5, 7, 17, 97, 257, 673}` with period `48`.
    have cover : ∀ r, r < 48 → ∃ p ∈ ([3, 5, 7, 17, 97, 257, 673] : List ℕ),
        (5292270077783 * 2 ^ r + 1) % p = 0 := by decide
    have h48all : ∀ p ∈ ([3, 5, 7, 17, 97, 257, 673] : List ℕ), (2 : ℕ) ^ 48 % p = 1 % p := by
      decide
    have hge2 : ∀ p ∈ ([3, 5, 7, 17, 97, 257, 673] : List ℕ), 2 ≤ p := by decide
    have hle : ∀ p ∈ ([3, 5, 7, 17, 97, 257, 673] : List ℕ), p ≤ 673 := by decide
    obtain ⟨p, hpS, hp0⟩ := cover (m % 48) (Nat.mod_lt m (by norm_num))
    -- Reduce the exponent modulo `48`.
    have h48 : (2 : ℕ) ^ 48 ≡ 1 [MOD p] := h48all p hpS
    have hred : (2 : ℕ) ^ m ≡ 2 ^ (m % 48) [MOD p] := by
      have key : (2 : ℕ) ^ m = (2 ^ 48) ^ (m / 48) * 2 ^ (m % 48) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod m 48]
      rw [key]
      simpa using (h48.pow (m / 48)).mul_right (2 ^ (m % 48))
    have hmod : (5292270077783 * 2 ^ m + 1) ≡ (5292270077783 * 2 ^ (m % 48) + 1) [MOD p] :=
      (hred.mul_left 5292270077783).add_right 1
    have hmod' : (5292270077783 * 2 ^ m + 1) % p = (5292270077783 * 2 ^ (m % 48) + 1) % p := hmod
    have hdvd : p ∣ 5292270077783 * 2 ^ m + 1 :=
      Nat.dvd_of_mod_eq_zero (hmod'.trans hp0)
    -- Hence `5292270077783 * 2 ^ m + 1` is composite, not prime.
    intro hprime
    rcases hprime.eq_one_or_self_of_dvd p hdvd with h1 | h2
    · have := hge2 p hpS; omega
    · have hbig : (673 : ℕ) < 5292270077783 * 2 ^ m + 1 := by
        have h2m : (2 : ℕ) ≤ 2 ^ m := by
          calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have := hle p hpS
      omega
  · show a 473165 < 5292270077783
    norm_num [a]
  · show (5292270077783 : ℕ) < a 473165 + 28
    norm_num [a]
