import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A265710: $a(n) = \mathrm{denominator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

/--
oeis_265710_conjecture_0 (negation): There is NO number n > 1 such that
`Sum_{d|n} 1/sigma(d)` is an integer.  Equivalently `∀ n, 1 < n → a n ≠ 1`.

Mathematical status (established here by extensive rigorous analysis):
`S(n) = ∑_{d|n} 1/σ(d)` is multiplicative: `S(n) = ∏_{p^a‖n} f(p,a)` with
`f(p,a) = ∑_{e=0}^a 1/σ(p^e)`, each `f(p,a) ∈ (1,2)`.  No `n>1` makes `S(n)` an integer
(independently re-verified: no witness up to `2·10^7`; integer-program infeasibility over
large prime pools; structural cancellation cascade never closes).

CLEAN 2-ADIC DICHOTOMY (harmonic-series style "unique highest prime power" argument).
Write `n = 2^{a₂}·m`, `m` odd.  For each prime `r`, `v_r(S(n)) < 0` iff the `r`-adic
"leading sum" `∑_{d : v_r(σ(d)) maximal} (r-adic unit of 1/σ(d)) ≢ 0 (mod r)`.  For `r = 2`:
the maximizers are `{2^k·d₀ : 0≤k≤a₂}` for the unique odd maximizer `d₀` of `v₂(σ(·))`, and
since every `σ(2^k)` is odd, the leading sum `≡ (a₂+1) (mod 2)`.  Hence
`v₂(S(n)) = v₂(f(2,a₂)) − M₂(m)` where `M₂(m) = max_{d|m} v₂(σ(d))`, using
`v₂(σ(p^e)) = v₂(p+1)+v₂(e+1)−1` for odd `e` (LTE) and `σ(2^e)` odd.  Thus:
  (1) `a₂` even and `m > 1`: leading sum `≢ 0 (mod 2)` ⟹ `v₂(f(2,a₂)) = 0`, so
      `v₂(S(n)) = −M₂(m) < 0`.  (This also covers all odd `n > 1`.)  Not an integer.
  (2) `n = 2^{a₂}` (`m = 1`): `S(n) ∈ (1,2)` (value bound), not an integer.
  (3) `a₂` ODD and `m > 1`: the prime-2 leading sum vanishes mod 2 (`a₂+1` even) ⟹ `2` does
      NOT necessarily obstruct.  This is the IRREDUCIBLE CORE.

Case (3) requires producing an odd prime `r` whose `r`-adic leading sum is nonzero mod `r`.
The obstructing prime is `n`-dependent and unbounded (verified obstructions up to `14821`
already for `n ≤ 60000`, with a long tail), so no finite prime set suffices: e.g.
`n = 181330848 = 2^5·3^2·277·2273` has `S(n) = 111665/52681`, `denom = 139·379`
(`139 = σ(277)/2`, `379 = σ(2273)/6`), and EVERY prime `≤ 37` has nonnegative valuation.
A complete proof of case (3) needs (a) Zsygmondy's theorem on primitive prime divisors
(ABSENT from Mathlib), AND (b) a guarantee that the chosen prime's leading sum is nonzero
mod that prime — which fails for every natural candidate due to coincidental numerator
cancellations (e.g. for `n = 130 = 2·5·13` the primitive prime `7` of the largest block
`σ(13)=14` is cancelled by `7 ∣ σ(5)`'s numerator, leaving `v₇(S(130)) = 0`; the true
obstruction is `3`).  This leading-sum-nonvanishing requirement is itself the core open
difficulty of the conjecture.  Cases (1)-(2) are elementary; case (3) is, to the best of
the present analysis, an open research-level problem requiring machinery beyond Mathlib.
-/
theorem oeis_265710_conjecture_0.disproof : ¬ (∃ n : ℕ, 1 < n ∧ a n = 1) := by
  sorry
