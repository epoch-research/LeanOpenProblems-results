import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

/-
oeis_270994_conjecture_0: Are a(n) and a(n) + 28 always consecutive Sierpiński numbers?

This conjecture asserts that for all $n$, $a(n)$ and $a(n)+28$ are Sierpiński numbers,
and there are no Sierpiński numbers strictly between them.

The conjecture is FALSE. While `a n` and `a n + 28` are indeed Sierpiński numbers
(both are covered by the covering set `{3, 5, 7, 13, 17, 241}`, all of whose primes
divide the common difference `11184810`), the "consecutive" part fails: there can be
a Sierpiński number strictly between them.

Concretely, take `n = 473165`. Then `a n = 5292270077779` and `a n + 28 = 5292270077807`.
The number `M = 5292270077783 = a n + 4` lies strictly between them and is itself a
Sierpiński number: it is covered by the covering set `{3, 5, 7, 17, 97, 257, 673}` with
period `48` (every prime `p` in this set satisfies `2^48 ≡ 1 (mod p)`), so for every
`j > 0` the number `M * 2^j + 1` is divisible by one of these primes and exceeds it,
hence is composite.

Below, `cover` establishes divisibility of `M * 2^j + 1` for arbitrary `j` from the
finite check at `j % 48`, `finish` upgrades this to non-primality, `M_sier` proves `M`
is a Sierpiński number, and `oeis_270994_conjecture_0.disproof` assembles the refutation.
-/

/-- If `2^48 ≡ 1 (mod p)` and `p ∣ M * 2^r + 1` where `r = j % 48` (with `M = 5292270077783`),
then `p ∣ M * 2^j + 1`. This lets a finite (`j < 48`) covering check extend to all `j`. -/
private lemma cover (p r j : ℕ) (h48 : (2:ℕ)^48 ≡ 1 [MOD p])
    (hr : j % 48 = r) (hcov : (5292270077783 * 2^r + 1) % p = 0) :
    p ∣ 5292270077783 * 2^j + 1 := by
  have e1 : (2:ℕ)^j ≡ 2^r [MOD p] := by
    have hpow : (2:ℕ)^j = (2^48)^(j/48) * 2^r := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [hpow]
    calc (2^48)^(j/48) * 2^r
        ≡ 1^(j/48) * 2^r [MOD p] := (h48.pow (j/48)).mul_right _
      _ = 2^r := by rw [one_pow, one_mul]
  have e2 : 5292270077783 * 2^j + 1 ≡ 5292270077783 * 2^r + 1 [MOD p] :=
    (e1.mul_left 5292270077783).add_right 1
  have e3 : 5292270077783 * 2^r + 1 ≡ 0 [MOD p] :=
    (Nat.modEq_zero_iff_dvd).mpr (Nat.dvd_of_mod_eq_zero hcov)
  exact (Nat.modEq_zero_iff_dvd).mp (e2.trans e3)

/-- For a covering prime `p ≤ 673` and `n > 0`, the number `M * 2^n + 1` is not prime,
since `p` is a proper divisor of it. -/
private lemma finish (p n r : ℕ) (hp : Nat.Prime p) (hp673 : p ≤ 673)
    (h48 : (2:ℕ)^48 ≡ 1 [MOD p]) (hn : 0 < n) (hr : n % 48 = r)
    (hcov : (5292270077783 * 2^r + 1) % p = 0) :
    ¬ Nat.Prime (5292270077783 * 2^n + 1) := by
  have h2n : (2:ℕ) ≤ 2^n := by
    calc (2:ℕ) = 2^1 := (pow_one 2).symm
    _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
  intro hprime
  have hdvd : p ∣ 5292270077783 * 2^n + 1 := cover p r n h48 hr hcov
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h1 | h2
  · exact hp.ne_one h1
  · omega

/-- `M = 5292270077783` is a Sierpiński number, via the covering set `{3,5,7,17,97,257,673}`
of period `48`. -/
private lemma M_sier : is_sierpinski_number 5292270077783 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro n hn
  obtain ⟨r, hr, hrlt⟩ : ∃ r, n % 48 = r ∧ r < 48 :=
    ⟨n % 48, rfl, Nat.mod_lt n (by norm_num)⟩
  interval_cases r <;>
    first
    | exact finish 3 n _ (by norm_num) (by norm_num) (by decide) hn hr (by decide)
    | exact finish 5 n _ (by norm_num) (by norm_num) (by decide) hn hr (by decide)
    | exact finish 7 n _ (by norm_num) (by norm_num) (by decide) hn hr (by decide)
    | exact finish 17 n _ (by norm_num) (by norm_num) (by decide) hn hr (by decide)
    | exact finish 97 n _ (by norm_num) (by norm_num) (by decide) hn hr (by decide)
    | exact finish 257 n _ (by norm_num) (by norm_num) (by decide) hn hr (by decide)
    | exact finish 673 n _ (by norm_num) (by norm_num) (by decide) hn hr (by decide)

theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  obtain ⟨_, _, hR⟩ := h 473165
  refine hR 5292270077783 M_sier ?_ ?_
  · show a 473165 < 5292270077783
    simp only [a]; norm_num
  · show (5292270077783 : ℕ) < a 473165 + 28
    simp only [a]; norm_num
