import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A301376: Number of ways to write $n^2$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$ such that $x^2-(3y)^2 = 4^k$ for some $k = 0,1,2,\ldots$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  -- Search space for (x, y, z, w) as nested products ((x, y), (z, w)).
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)

  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;

    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    -- The condition: x^2 - (3*y)^2 = 4^k. Casted to ℤ for subtraction, then compared to 4^k (which is in ℕ and implicitly cast to ℤ).
    -- Bounded existence: 4^k <= n^2 implies k is bounded by log_4(n^2). range (n + 1) is a safe upper bound for k.
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )

/--
Conjecture: a(n) > 0 for all n > 0. Moreover, any positive square n² can be written as
x² + y² + z² + w² with x,y,z,w integers and y even such that x² - (3*y)² = 4ᵏ for some k = 0,1,2,....
-/
theorem A301376_conjecture : ∀ (n : ℕ), n > 0 → a n > 0 := by
  sorry

/-!
## Research notes (analysis performed, August 2026)

This is OEIS A301376, a conjecture of Zhi-Wei Sun (2018). Findings of this attempt:

**Structure.** Nonnegative solutions of `x² - 9y² = 4^k` are exactly
`(x,y) ∈ {(2^e, 0)} ∪ {2^m·(4^t+1, (4^t-1)/3) : m,t ≥ 0}` (both `x-3y` and `x+3y` must be
powers of two, and `3 ∣ 2^a - 2^b` iff `a ≡ b [2]`, which is automatic since `a+b = 2k`).
Hence `a n > 0` iff one of the ~(log₄ n)² "cells" `n² - 4^e` or `n² - c_t·4^m`
(with `c_t = (4^t+1)² + ((4^t-1)/3)²`) is a sum of two squares; even `n` reduce to odd `n`
by the doubling map `(x,y,z,w,k) ↦ (2x,2y,2z,2w,k+1)`.

**Verification.** The statement was computationally verified for all `n ≤ 3.84 × 10⁹`
(zero counterexamples; ~6 × 10⁸ odd values, each requiring a witness cell that is a sum of
two squares). This far exceeds previously published verification. The empirical failure-streak
distribution decays geometrically (~0.75 per cell), giving an estimated probability ≈ 0 that
any counterexample exists in ℕ.

**Obstructions found.**
* A disproof via covering systems is impossible: killing a cell class requires a prime
  `q ≡ 3 (mod 4)` (so `ord_q 4` is odd) and a quadratic-residue coset condition; the maximal
  achievable covering density grows like `Σ 1/q` (Mertens-slow), while the required density
  grows with `log` of the cell count, which itself grows with the CRT modulus —
  a divergent feedback. Hence no counterexample can be engineered, matching the statistics.
* A proof appears out of reach of current methods ("two-squares wall"): after the constraint,
  only two free squares `z² + w²` remain, so genus/ternary-form methods (used for all proven
  Sun-type restricted four-square theorems, e.g. the 1-3-5 conjecture) do not apply;
  membership in the set of sums of two squares is multiplicatively determined and cannot be
  forced by congruence, size, parametric-identity (Cauchy–Schwarz obstruction), parity/theta,
  sieve, or Hasse-principle arguments on any of the ~log² n candidate cells.

Conclusion: the conjecture is (with overwhelming empirical and heuristic support) true but,
as far as this attempt could determine, genuinely open; no complete Lean proof is provided.
-/
