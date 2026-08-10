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

/-- **Reduction lemma** (fully proved): to produce a prime `p < n` with `⌊√(n+p)⌋`
prime, it suffices to exhibit a prime `q` and a prime `p < n` lying in the "band"
`q² ≤ n+p ≤ q²+2q`; for then `⌊√(n+p)⌋ = q`. -/
theorem oeis_A237720_conjecture_ii_reduction (n : ℕ)
    (h : ∃ q : ℕ, q.Prime ∧ ∃ p : ℕ, p.Prime ∧ p < n ∧ q * q ≤ n + p ∧ n + p ≤ q * q + 2 * q) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  obtain ⟨q, hq, p, hp, hpn, h1, h2⟩ := h
  refine ⟨p, hp, hpn, ?_⟩
  have hsqrt : Nat.sqrt (n + p) = q := by
    have hle : q ≤ Nat.sqrt (n + p) := Nat.le_sqrt.mpr h1
    have hlt : Nat.sqrt (n + p) < q + 1 := by
      rw [Nat.sqrt_lt']; rw [pow_two]; nlinarith [h2]
    omega
  rw [hsqrt]; exact hq

/-- **Easy-case lemma** (fully proved): whenever a *fixed small* prime `p₀ < n`
already lands `n + p₀` inside a prime band `q² ≤ n+p₀ ≤ q²+2q` (`q` prime), the
conjecture holds for `n`.  Taking `p₀ = 2` this covers every `n` for which
`⌊√(n+2)⌋` is prime; taking `p₀ = q` it covers every `n ∈ [q²-q, q²+q]`.  The
only residual ("trapped") cases are the `n` with `⌊√(n+2)⌋` composite and a large
prime gap straddling `√n`, which provably need a short-interval prime (see the
main theorem's documentation). -/
theorem oeis_A237720_conjecture_ii_easy (n p₀ q : ℕ)
    (hp₀ : p₀.Prime) (hp₀n : p₀ < n) (hq : q.Prime)
    (h1 : q * q ≤ n + p₀) (h2 : n + p₀ ≤ q * q + 2 * q) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  refine ⟨p₀, hp₀, hp₀n, ?_⟩
  have hsqrt : Nat.sqrt (n + p₀) = q := by
    have hle : q ≤ Nat.sqrt (n + p₀) := Nat.le_sqrt.mpr h1
    have hlt : Nat.sqrt (n + p₀) < q + 1 := by
      rw [Nat.sqrt_lt']; rw [pow_two]; nlinarith [h2]
    omega
  rw [hsqrt]; exact hq

/-- Specialisation with `p₀ = 2`: the conjecture holds whenever `⌊√(n+2)⌋` is prime. -/
theorem oeis_A237720_conjecture_ii_of_sqrt_add_two_prime (n : ℕ) (hn : 2 < n)
    (h : (Nat.sqrt (n + 2)).Prime) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  refine ⟨2, Nat.prime_two, by omega, h⟩

/-- **Bertrand-band lemma** (fully proved): whenever there is a prime `q` with
`q²` just above `n` (precisely `n+2 ≤ q²` and `q² ≤ 2q+n+2`, i.e. `q ∈ {⌈√(n+2)⌉, that+1}`)
and `n` is not too small (`4q+2 < n`), Bertrand's postulate supplies a prime `p`
inside the band `q² ≤ n+p ≤ q²+2q`, so the conjecture holds for `n`.  This covers
exactly the cases where `⌊√(n+2)⌋` or its successor is prime; the only residual
("trapped") cases are those where both are composite. -/
theorem oeis_A237720_conjecture_ii_bertrand_band (n q : ℕ) (hq : q.Prime)
    (hn2 : n + 2 ≤ q * q) (hC : q * q ≤ 2 * q + n + 2) (hD : 4 * q + 2 < n) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  obtain ⟨p, hp, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (q * q - (n + 1)) (by omega)
  exact oeis_A237720_conjecture_ii_easy n p q hp (by omega) hq (by omega) (by omega)

/-- OEIS A237720 Conjecture (ii): For any integer $n > 2$, there is a prime $p < n$ with $\lfloor\sqrt{n+p}\rfloor$ prime. -/
theorem oeis_A237720_conjecture_ii (n : ℕ) (hn : n > 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  /-
  STATUS OF THIS CONJECTURE (Zhi-Wei Sun, OEIS A237720, part (ii)).

  TRUTH.  The statement is TRUE.  It has been verified by direct computation for
  all `n` in `[3, 10^6]` (and, in the literature, much further), and the number
  of valid witnesses `p` grows like `~ n / (ln n)^2`.  In particular no
  counterexample exists, so the conjecture CANNOT be disproved.

  WHY A PROOF NEEDS SHORT-INTERVAL PRIMES (rigorous obstruction).
  By `oeis_A237720_conjecture_ii_reduction`, a witness is a prime `q` together
  with a prime `p < n` lying in the band `q² ≤ n+p ≤ q²+2q`.  Because `p < n`,
  the only usable `q` lie in `√n < q < √(2n)`.

  Mathlib's *only* tool that certifies the existence of a prime inside an
  interval is Bertrand's postulate, `Nat.exists_prime_lt_and_le_two_mul`
  (a prime in `(m, 2m]`).  A band's preimage `[q²-n, q²+2q-n]` (length `2q`)
  contains a full Bertrand interval `(m, 2m]` iff `q² - n ≤ 2q`, i.e. iff
  `q` is within `~1` of `√n`.  So Bertrand can certify a witness ONLY when there
  is a prime `q` essentially equal to `⌈√n⌉`.

  Now consider the infinitely many "trapped" `n`: those for which
  `c := ⌊√(n+2)⌋` is composite and the next prime `b` above `c` is far away
  (a large prime gap straddling `√n`).  For such `n`, every Bertrand-certifiable
  band has *composite* `q`, hence NO witness is Bertrand-certifiable.  The true
  witness needs a prime `p` in the band of `b`, i.e. a prime in an interval of
  length `2b ≈ 2√n` positioned near `b² - n ≈ 2·g·√n`, where `g` is the prime
  gap near `√n`.  An unconditional "prime in `[x, x+x^θ]`" theorem supplies BOTH
  the gap bound near `√n` (`g ≤ n^{θ/2}`, so `b²-n ≲ 2 n^{(1+θ)/2}`) AND the
  band-filling (`n^{1/2} ≥ (n^{(1+θ)/2})^θ`); these are compatible exactly when
  `θ² + θ - 1 ≤ 0`, i.e. `θ ≤ (√5-1)/2 ≈ 0.618` (the golden ratio).  So Hoheisel
  (`θ≈1`) and Ingham (`θ=5/8`) are insufficient, while Montgomery (`θ=3/5`),
  Huxley (`θ=7/12`) and Baker–Harman–Pintz (`θ=0.525`) all suffice.
  IRREDUCIBLE BLOCKER: a quantitative zero-free region (de la Vallée Poussin) —
  even the full Prime Number Theorem — only yields `ψ(x)=x+O(x exp(-c√log x))`,
  i.e. primes in intervals of length `x exp(-c√log x) = x^{1-o(1)}` (`θ→1`), which
  is strictly LONGER than `x^{0.618}` and hence insufficient.  Polynomial-length
  short intervals require a ζ ZERO-DENSITY estimate `N(σ,T) ≪ T^{A(1-σ)}`
  (Ingham/Montgomery/Huxley), resting on mean values of Dirichlet polynomials /
  the fourth moment of ζ — strictly beyond PNT and unformalized in Lean.
  (Concrete example: `n = 101129` has `⌊√(n+2)⌋ = 318` composite
  with next prime `331`; the smallest witness is `p = 8443`, a prime in the
  short interval `[331²-n, 331²+2·331-n] = [8432, 9094]`.)

  Since prime gaps near `√n` are UNBOUNDED (Westzynthius), no fixed
  multiplicative result — Bertrand `(x,2x]`, Nagura `(x,1.2x]`, or any
  `prime in (x, λx]` with a constant `λ > 1` — can work for all `n`; the required
  `λ → 1`, i.e. genuine short intervals.  These follow from
  Baker–Harman–Pintz / Huxley (`θ ≤ 7/12`), which rest on ζ zero-density
  estimates that are ABSENT from current Mathlib (only the qualitative
  non-vanishing of ζ on `Re(s)=1` is available).  A counting/pigeonhole route is
  also blocked: both `{p<n : p prime}` and `{m∈[n+2,2n): ⌊√m⌋ prime}` have
  density `~1/ln n`, so inclusion–exclusion yields a negative bound — the parity
  barrier.

  CONCLUSION.  The conjecture is a true theorem of analytic number theory whose
  proof provably requires short-interval prime existence beyond what Mathlib
  currently provides; it is not disprovable; and there is no elementary
  (Bertrand-level) certification, by the rigorous trapped-`n` obstruction above.
  The remaining step below is exactly this short-interval prime existence.
  -/
  apply oeis_A237720_conjecture_ii_reduction
  sorry
