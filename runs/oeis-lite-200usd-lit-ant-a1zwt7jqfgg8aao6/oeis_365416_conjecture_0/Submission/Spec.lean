import FormalConjectures.Util.ProblemImports

open Nat

/--
Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers (A246655).
-/
def A365416_condition (k : ℕ) : Prop :=
  IsPrimePow (2 * k - 1) ∧ IsPrimePow (2 * k + 1)

/--
The $n$-th term of A365416 (Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers).
Defined for $n \ge 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (n - 1).nth A365416_condition

-- Formalization of the conjecture

/--
Predicate for a number to be a prime power with exponent strictly greater than 1.
This is equivalent to being a composite prime power (a perfect power whose base is prime).
-/
def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

/--
The key Diophantine input.

If `p^e` and `q^f` are prime powers with exponents `e, f ≥ 2` whose difference is
exactly `2` (i.e. `q^f = p^e + 2`), then `(p, e, q, f) = (5, 2, 3, 3)`, i.e. the
only such pair is `25 = 5^2` and `27 = 3^3`.

Equivalently: `25` and `27` are the only prime powers (with exponent `> 1`) that
differ by `2`.  This is a theorem (Scott–Styer 2013; Bennett–Siksek 2021): writing
`q^f - p^e = 2` and reducing modulo `4` forces the number `≡ 3 (mod 4)` to have an
odd exponent, and one is led to the three families

* `X^2 + 2 = y^n` (one number is a perfect square, the smaller one);
* `X^2 - 2 = y^n` (one number is a perfect square, the larger one);
* `u^ℓ + 2 = w^m` with `ℓ ≠ m` odd primes (neither is a square).

The first is the classical Lebesgue equation, solved elementarily in `ℤ[√-2]`
(units `±1`, class number `1`), yielding only `(X, y, n) = (5, 3, 3)`.  The other two
families have no solutions, but the only known proofs rely on Baker's lower bounds
for linear forms in (`p`-adic and complex) logarithms together with the modularity
of the Galois representations attached to Frey–Hellegouarch elliptic curves
(see Bennett–Siksek, *Differences between perfect powers: prime power gaps*).
-/
theorem prime_pow_gap_two
    {p e q f : ℕ} (hp : Nat.Prime p) (he : 1 < e) (hq : Nat.Prime q) (hf : 1 < f)
    (hgap : q ^ f = p ^ e + 2) : p = 5 ∧ e = 2 ∧ q = 3 ∧ f = 3 := by
  sorry

/-- Prime powers with exponent `> 1` are at least `4`. -/
private lemma four_le_prime_pow {p e : ℕ} (hp : Nat.Prime p) (he : 1 < e) :
    4 ≤ p ^ e := by
  have h1 : 2 ^ 2 ≤ p ^ e :=
    (Nat.pow_le_pow_left hp.two_le 2).trans (Nat.pow_le_pow_right hp.pos (by omega))
  simpa using h1

/--
A365416 According to Pillai's conjecture, k = 13 is the only term such that 2*k-1 and 2*k+1 both have exponent greater than 1.
-/
theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  intro k
  constructor
  · -- Forward direction: extract the prime-power data and apply the gap theorem.
    rintro ⟨⟨p, e, hp, he, hpe⟩, ⟨q, f, hq, hf, hqf⟩⟩
    -- The smaller number is at least 4, so in particular `2 * k - 1 ≥ 4`.
    have hb : 4 ≤ 2 * k - 1 := hpe ▸ four_le_prime_pow hp he
    -- Hence `2 * k + 1 = (2 * k - 1) + 2`, giving `q ^ f = p ^ e + 2`.
    have hgap : q ^ f = p ^ e + 2 := by
      rw [hqf, hpe]; omega
    obtain ⟨hp5, he2, hq3, hf3⟩ := prime_pow_gap_two hp he hq hf hgap
    -- Now `2 * k - 1 = p ^ e = 25`, forcing `k = 13`.
    have : 2 * k - 1 = 25 := by rw [← hpe, hp5, he2]; norm_num
    omega
  · -- Backward direction: `k = 13` gives `25 = 5 ^ 2` and `27 = 3 ^ 3`.
    rintro rfl
    exact ⟨⟨5, 2, by norm_num, by norm_num, by norm_num⟩,
           ⟨3, 3, by norm_num, by norm_num, by norm_num⟩⟩
