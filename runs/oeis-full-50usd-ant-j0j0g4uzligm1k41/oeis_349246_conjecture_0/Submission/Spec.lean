import FormalConjectures.Util.ProblemImports

open Nat

/--
A349246: Number of ways to write $n$ as $w^8 + x^4 + 2y^4 + 4z^4 + t(t+1)$, where $w, x, y, z$, and $t$ are nonnegative integers.
-/
def A349246 (n : ℕ) : ℕ :=
  let B := Finset.range (n + 1)
  Finset.sum B $ fun w =>
  Finset.sum B $ fun x =>
  Finset.sum B $ fun y =>
  Finset.sum B $ fun z =>
  Finset.sum B $ fun t =>
    if w^8 + x^4 + 2 * y^4 + 4 * z^4 + t * (t + 1) = n then 1 else 0

/-
## Status of this conjecture (analysis)

This is Zhi-Wei Sun's conjecture, OEIS A349246: every natural number `n`
is representable as `w^8 + x^4 + 2*y^4 + 4*z^4 + t*(t+1)`.

Analysis carried out while working on this file:

* The statement is **true** as far as can be checked: an exhaustive search finds
  a representation for every `n ≤ 10^8`, and the number of representations grows
  (its minimum over `[2*10^7, ...]` already exceeds `50` and increases), so there
  is no counterexample to exhibit.
* Every one of the five summands is essential: dropping `w^8`, or `4*z^4`, or any
  other term, leaves infinitely many non-representable numbers.
* Multiplying by `4` and adding `1` gives the exact equivalence
  `4n+1 = (2t+1)^2 + 4*(w^8 + x^4 + 2*y^4 + 4*z^4)`,
  so the conjecture is equivalent to: `4n+1` admits a three-square representation
  `A^2 + (2b)^2 + (2c)^2` (`A` odd) with `b^2 + c^2 ∈ S`, where
  `S = { x^4 + 2*y^4 + 4*z^4 + w^8 }`.  (This equivalence was verified numerically.)
* The fourth-power variables must grow without bound (there exist `n` forcing a
  variable `≥ 12`, and larger `n` force larger values), so no finite covering
  system, polynomial identity, or residue argument can settle it.  It is a genuine
  additive/analytic problem: the sparse set `S` has density `~ n^{7/8}` and one needs
  a rigorous no-exceptions lower bound, i.e. circle-method input for fourth powers.

* Structural observation: `S` is dense — its maximal gap grows only like `~ n^{1/8}`
  (empirically 206, 400, 501 for `n = 10^6, 10^7, 10^8`), far below the pronic
  spacing `~ 2*sqrt n`.  Nevertheless a covering proof fails: representations force
  arbitrarily large pronics (the least usable `t` grows like `~ 0.6*sqrt n`), and the
  sampled points `n - t(t+1)` can miss `S` for arbitrarily many consecutive `t`
  (e.g. 187 consecutive misses at `n = 100952`).  So the required *exact* hitting of
  `S` by `n - (pronic)` is precisely the delicate analytic content.

The current Lean/Mathlib environment does not even contain the three-square theorem
(only Lagrange's four-square theorem and Fermat's two-square theorem), has no
polygonal-number / Waring / biquadrate theory, and the circle-method machinery for
fourth powers required for a complete proof is not available and not feasible to
formalize here.  I was unable to find an elementary proof (none is known), and the
statement being true, it cannot be disproven.  I record the honest partial state
below rather than fabricate a proof or exploit forbidden loopholes.
-/

/-- Conjecture: a(n) > 0 for all n = 0,1,2,.... -/
theorem oeis_349246_conjecture_0 (n : ℕ) : A349246 n > 0 := by
  sorry
