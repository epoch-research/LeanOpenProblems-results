import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Nat.Prime

/--
A237720: Number of primes $p \le \lfloor (n+1)/2 \rfloor$ with $\lfloor \sqrt{n-p} \rfloor$ prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ =>
    p.Prime ∧
    2 * p ≤ n + 1 ∧
    (Nat.sqrt (n - p)).Prime
  ) (Finset.range (n + 1)))

/-!
### Reduction of OEIS A237720 Conjecture (ii)

Requiring `(Nat.sqrt (n + p)).Prime` is, by definition of `Nat.sqrt`, the same as asking for a
prime `q` with `q^2 ≤ n + p ≤ q^2 + 2*q` (i.e. `q^2 ≤ n+p < (q+1)^2`).  So the conjecture is
*equivalent* to: for every `n > 2` there are primes `p < n` and `q` with
`q^2 ≤ n + p ≤ q^2 + 2*q`.

Since `p < n` forces `q^2 ≤ n + p < 2*n` and `(q+1)^2 > n + p ≥ n + 2`, any usable `q` satisfies
`√(n+2) - 1 < q < √(2n)`, i.e. `q ≈ √n`.  For such a `q` the admissible `p` form the interval
`[q^2 - n, q^2 + 2*q - n]` of width `2*q ≈ 2*√n`, located at scale `q^2 - n` which can be as large
as a constant times `n`.  Guaranteeing a prime in such an interval is a *primes-in-short-intervals*
statement of Baker–Harman–Pintz / Cramér strength (the source paper arXiv:1402.6641 of Zhi-Wei Sun
explicitly derives such conjectures from the unproven bound `p_{k+1} - p_k = O(√p_k · log p_k)`).

Bertrand's postulate — the only prime-existence result available in Mathlib — can only produce a
prime inside an interval of ratio `≥ 2`, which here would require a prime within distance `≈ 1` of
`√n` (Legendre's conjecture, open).  For instance at `n = 12994` (where `√n ≈ 114` lies in the
prime gap `[113, 127]`) every admissible window has ratio `≤ 1.08`, so no interval theorem of any
*fixed* ratio can settle it.  Consequently the analytic core `exists_prime_window` below is the
single irreducible input; the remainder of the argument is fully formalized. -/

/-- If `q^2 ≤ m ≤ q^2 + 2*q` then `Nat.sqrt m = q` (i.e. `q^2 ≤ m < (q+1)^2`). -/
lemma sqrt_of_window {m q : ℕ} (h1 : q * q ≤ m) (h2 : m ≤ q * q + 2 * q) :
    Nat.sqrt m = q := by
  have hm : m = q * q + (m - q * q) := (Nat.add_sub_cancel' h1).symm
  rw [hm]
  apply Nat.sqrt_add_eq
  omega

/-- **The Bertrand-provable case.**  If `q = ⌈√n⌉` is prime (encoded as `(q-1)^2 < n ≤ q^2`) and
`q ≥ 7`, then the admissible window `[q^2 - n, q^2 + 2*q - n]` (of width `2*q`) provably contains a
prime `p < n`: when `q^2 = n` take `p = 2`, otherwise apply Bertrand's postulate at `q^2 - n`
(this lands inside the window precisely because `q^2 - n ≤ 2*q - 2 < 2*q`). -/
lemma window_of_prime_ceil (n q : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q)
    (h1 : (q - 1) * (q - 1) < n) (h2 : n ≤ q * q) :
    ∃ p : ℕ, p.Prime ∧ p < n ∧ q * q ≤ n + p ∧ n + p ≤ q * q + 2 * q := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hexp : (m + 1 - 1) * (m + 1 - 1) + 2 * (m + 1) = (m + 1) * (m + 1) + 1 := by
    simp only [Nat.add_sub_cancel]; ring
  have hbig : 6 * (m + 1) ≤ (m + 1) * (m + 1) := by nlinarith [hq7]
  by_cases hA0 : (m + 1) * (m + 1) - n = 0
  · exact ⟨2, Nat.prime_two, by omega, by omega, by omega⟩
  · obtain ⟨p, hp, hpA, hp2A⟩ :=
      Nat.exists_prime_lt_and_le_two_mul ((m + 1) * (m + 1) - n) hA0
    exact ⟨p, hp, by omega, by omega, by omega⟩

set_option maxRecDepth 8000 in
/-- Small cases `3 ≤ n < 49` verified by a finite decision procedure. -/
lemma exists_prime_window_small (n : ℕ) (hn3 : 3 ≤ n) (hn49 : n < 49) :
    ∃ q p : ℕ, q.Prime ∧ p.Prime ∧ p < n ∧ q * q ≤ n + p ∧ n + p ≤ q * q + 2 * q := by
  have key : ∀ n, 3 ≤ n → n < 49 →
      ∃ q < 10, ∃ p < 49, q.Prime ∧ p.Prime ∧ p < n ∧
        q * q ≤ n + p ∧ n + p ≤ q * q + 2 * q := by
    decide
  obtain ⟨q, _, p, _, hq, hp, hpn, hlo, hhi⟩ := key n hn3 hn49
  exact ⟨q, p, hq, hp, hpn, hlo, hhi⟩

/-- For every `n > 2` there exist primes `p < n` and `q` with `q^2 ≤ n + p ≤ q^2 + 2*q`
(equivalent to the conjecture).  Everything is proved **except** the case where `⌈√n⌉` is
composite: there the smallest admissible prime `q` can be far above `√n`, forcing us to find a
prime in an interval of width `2*q ≈ 2√n` located at a scale that may be a constant fraction of
`n`.  That is a *primes-in-short-intervals* statement of Baker–Harman–Pintz / Cramér strength,
which is strictly stronger than Bertrand's postulate (the only prime-existence tool in Mathlib)
and is not currently available.  Concretely, `n = 12994` (with `⌈√n⌉ = 114` composite, sitting in
the prime gap `[113, 127]`) needs a prime in `[3135, 3389]` — a window of ratio `≈ 1.08` that no
`fixed`-ratio interval theorem can guarantee. -/
lemma exists_prime_window (n : ℕ) (hn : n > 2) :
    ∃ q p : ℕ, q.Prime ∧ p.Prime ∧ p < n ∧ q * q ≤ n + p ∧ n + p ≤ q * q + 2 * q := by
  rcases lt_or_ge n 49 with hsmall | hbig
  · exact exists_prime_window_small n (by omega) hsmall
  · -- `n ≥ 49`, so `⌊√n⌋ ≥ 7` and hence `⌈√n⌉ ≥ 7`.
    obtain ⟨s, hs, hsle, hlt⟩ : ∃ s, s = Nat.sqrt n ∧ s * s ≤ n ∧ n < (s + 1) * (s + 1) :=
      ⟨Nat.sqrt n, rfl, Nat.sqrt_le n, Nat.lt_succ_sqrt n⟩
    have hs7 : 7 ≤ s := by
      by_contra h
      push_neg at h
      interval_cases s <;> omega
    by_cases he : s * s = n
    · -- `⌈√n⌉ = s`
      by_cases hqp : s.Prime
      · have hb1 : (s - 1) * (s - 1) < n := by
          obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
          simp only [Nat.add_sub_cancel]; nlinarith
        obtain ⟨p, hp, hpn, hlo, hhi⟩ := window_of_prime_ceil n s hqp hs7 hb1 (by omega)
        exact ⟨s, p, hqp, hp, hpn, hlo, hhi⟩
      · -- `⌈√n⌉ = s` composite: OPEN (primes in short intervals, BHP/Cramér strength)
        sorry
    · -- `⌈√n⌉ = s + 1`
      by_cases hqp : (s + 1).Prime
      · have hb1 : (s + 1 - 1) * (s + 1 - 1) < n := by simp only [Nat.add_sub_cancel]; omega
        obtain ⟨p, hp, hpn, hlo, hhi⟩ :=
          window_of_prime_ceil n (s + 1) hqp (by omega) hb1 (by omega)
        exact ⟨s + 1, p, hqp, hp, hpn, hlo, hhi⟩
      · -- `⌈√n⌉ = s + 1` composite: OPEN (primes in short intervals, BHP/Cramér strength)
        sorry

/-- OEIS A237720 Conjecture (ii): For any integer $n > 2$, there is a prime $p < n$ with $\lfloor\sqrt{n+p}\rfloor$ prime. -/
theorem oeis_A237720_conjecture_ii (n : ℕ) (hn : n > 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  obtain ⟨q, p, hq, hp, hpn, h1, h2⟩ := exists_prime_window n hn
  exact ⟨p, hp, hpn, by rw [sqrt_of_window h1 h2]; exact hq⟩
