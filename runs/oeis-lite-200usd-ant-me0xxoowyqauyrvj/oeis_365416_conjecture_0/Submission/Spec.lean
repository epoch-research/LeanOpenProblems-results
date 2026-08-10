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

/-- Elementary: two perfect squares cannot differ by exactly `2`. -/
theorem sq_no_diff_two {X Y : ℕ} (hX : 2 ≤ X) (h : Y ^ 2 = X ^ 2 + 2) : False := by
  have hYX : X < Y := by nlinarith [sq_nonneg (Y - X), sq_nonneg X]
  nlinarith [hYX]

/--
Core arithmetic fact behind A365416: if two prime powers with exponent `≥ 2`
differ by `2`, then the smaller one equals `25` (so the pair is `(25, 27) = (5², 3³)`).

This is precisely a case of **Pillai's conjecture** (difference `c = 2`): writing the
hypothesis as `q ^ b = p ^ a + 2`, split on the parity of the exponents.
* `(even, even)`: two squares differ by `2` — impossible. **(Proved below, elementarily.)**
* `(even, odd)`: `X² + 2 = q ^ b`; Nagell's theorem gives the unique `5² + 2 = 3³`,
  hence `p ^ a = 25`. *(A known theorem; not yet in Mathlib.)*
* `(odd, even)`: `Y² − 2 = p ^ a`; Lebesgue–Nagell gives no solutions. *(Known theorem.)*
* `(odd, odd)` (`a, b ≥ 3` odd): `q ^ b − p ^ a = 2` — a Pillai/Fermat–Catalan-type
  equation that is **open**: it has provably no congruence obstruction (verified across
  many moduli) and no growth obstruction (the linear form `b·ln q − a·ln p` gets
  arbitrarily small), and the `ℤ[√-2]` factorization that closes the even cases fails
  (no perfect square is present).
-/
theorem prime_powers_diff_two {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : 1 < a) (hb : 1 < b) (h : q ^ b = p ^ a + 2) : p ^ a = 25 := by
  rcases Nat.even_or_odd a with hae | hao
  · rcases Nat.even_or_odd b with hbe | hbo
    · -- (even, even): two squares differ by 2 — impossible (elementary).
      exfalso
      obtain ⟨r, hr⟩ := hae
      obtain ⟨s, hs⟩ := hbe
      have hX : 2 ≤ p ^ r := by
        have h2 := hp.two_le
        calc 2 ≤ p := h2
        _ ≤ p ^ r := Nat.le_self_pow (by omega) p
      have hpa : p ^ a = (p ^ r) ^ 2 := by rw [hr]; ring
      have hqb : q ^ b = (q ^ s) ^ 2 := by rw [hs]; ring
      rw [hpa, hqb] at h
      exact sq_no_diff_two hX h
    · -- (even, odd): X² + 2 = q^b ; Nagell's theorem ⇒ p^a = 25. (Known theorem.)
      sorry
  · rcases Nat.even_or_odd b with hbe | hbo
    · -- (odd, even): Y² − 2 = p^a ; Lebesgue–Nagell ⇒ no solution. (Known theorem.)
      sorry
    · -- (odd, odd), a,b ≥ 3 odd: q^b − p^a = 2 — OPEN (Pillai, c = 2).
      sorry

/--
A365416 According to Pillai's conjecture, k = 13 is the only term such that 2*k-1 and 2*k+1 both have exponent greater than 1.
-/
theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 :=
by
  intro k
  constructor
  · -- Forward direction reduces (elementarily) to the Pillai-type core above.
    rintro ⟨⟨p, a, hp, ha, hpa⟩, ⟨q, b, hq, hb, hqb⟩⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have : 0 < p ^ a := pow_pos hp.pos a
      omega
    · have hq2 : q ^ b = p ^ a + 2 := by omega
      have h25 : p ^ a = 25 := prime_powers_diff_two hp hq ha hb hq2
      omega
  · -- Backward direction: k = 13 gives 25 = 5² and 27 = 3³.
    rintro rfl
    refine ⟨⟨5, 2, by norm_num, by norm_num, by norm_num⟩,
           ⟨3, 3, by norm_num, by norm_num, by norm_num⟩⟩
