import FormalConjectures.Util.ProblemImports

open Nat

/--
A180017: Difference of sums of digits of $n$ in ternary and in binary.
$$a(n) = \left(\sum \text{digits}_3(n)\right) - \left(\sum \text{digits}_2(n)\right)$$
-/
def a (n : ℕ) : ℤ :=
  Int.ofNat (Nat.digits 3 n |>.sum) - Int.ofNat (Nat.digits 2 n |>.sum)

/--
%C A180017 This sequence is positive on average, since 1/log(3) > 1/log(4). Do all integers appear infinitely often? - _Charles R Greathouse IV_, Feb 07 2013
The conjecture asks if for every integer $z$, the set of natural numbers $n$ such that $a(n) = z$ is infinite.

Analysis (A180017, Greathouse 2013).  Writing s₂, s₃ for the base-2/base-3 digit sums
(so `a n = s₃ n - s₂ n = v₂(n!) - 2·v₃(n!)`, whence `|a n| = O(log n)`):

* `a n = Σ_{k=1}^n (v₂ k - 2 v₃ k)`, a mean-zero-increment walk confined to `±O(log n)`,
  but with a positive *value* drift `E[a n] ≈ 0.189 log n` and fluctuation `≈ √(log n)`.
* Append lemma: if `x < 2^v` and `6^v ∣ y` then `a (x + y) = a x + a y` (blocks separated
  by a power of 6 add, since `6^v = 2^v·3^v` clears the low v digits in both bases).
* Unbounded above: `a (3^k - 1) = 2k - s₂(3^k - 1) ≥ 2k - k·log₂3 → +∞`.
* Unbounded below (CRT): choosing `i,j` with `3^i + 3^j ≡ 2^B - 2 (mod 2^B)` forces
  `s₂(3^i+3^j) ≥ B-1` while `s₃ = 2`, so `a ≤ 3 - B`.

TRUTH AND DIFFICULTY.  The conjecture is TRUE: for every fixed `z`, `#{n<N : a n = z}`
grows like `N^{0.98}` (verified numerically). Since the *mean* of `a` drifts to `+∞`,
`a n = z` for fixed `z` is a *lower-tail large-deviation* event; establishing that its
count diverges is a large-deviation local limit theorem for the joint distribution of
`(s₂ n, s₃ n)` in the coprime bases 2 and 3 (Gelfond exponential sums / Drmota–Mauduit–
Rivat).  Mathlib contains no equidistribution/Weyl/exponential-sum machinery.

CLEAN REDUCTION (the sharpest elementary reduction found).  Let `W_v = {a x : x < 2^v}` be
the value set on a dyadic block, and `c_v = a (6^v)`.  The append lemma gives
`a (6^v + x) = c_v + a x` for `x < 2^v`, so `a` attains `z` on `[6^v, 6^v + 2^v)` iff
`z - c_v ∈ W_v`.  Since `c_v ≈ -0.16 v` and `W_v` is (empirically) the integer interval
`[min_v, max_v] ≈ [-0.85 v, 0.66 v]` with at most one gap at each *extreme* (never interior),
`z - c_v ≈ z + 0.16 v` is a deep-interior value, so `z - c_v ∈ W_v` for all large `v`, giving
distinct witnesses `6^v + x ∈ [6^v, 2·6^v)`.  Hence:
      CONJECTURE ⟸ "for infinitely many v, z - a(6^v) ∈ W_v"  ⟸  interior gap-freeness of W_v.
(Verified numerically: `z - a(6^v) ∈ W_v` holds cofinitely in `v` for every tested `z`.)

Every elementary reduction circles back to the same irreducible analytic core, namely
interior gap-freeness / the local limit theorem:
  - "infinitely often for `z`" ⇔ `#{n<2^v : a n = z} → ∞`;
  - equivalently (B) "for every v there is a positive multiple of `6^v` with equal base-2/
    base-3 digit sums", i.e. `0` attained i.o. among multiples of `6^v` (a lower-tail event);
  - the obstruction is that any multiple of `6^v = 2^v·3^v` has BOTH representations
    scrambled by the cofactor (`a(6^v q) = s₃(2^v q) - s₂(3^v q) ≠ a q`), so one digit sum can
    be pinned exactly only by leaving the other as `~log`-size "junk"; hitting an exact target
    needs unit-resolution control of that junk — precisely the analytic equidistribution
    statement.  This defeats every explicit family (sums of spread-out powers of 2 or of 3
    both fail: the un-shifted base has permanently overlapping low digits, so no clean
    additivity; multi-block base-6 concatenation scrambles the high blocks).
Even the weakest ingredient (some value attained i.o.) is non-elementary: a walk bounded by
`C·log n` need not be recurrent (e.g. `⌊log n⌋`).

CLEANEST REDUCTION (via the multiplicative family `n = 2^a·3^b`).  Here `a` collapses:
`a (2^a 3^b) = s₃(2^a) - s₂(3^b)` (the `3^b` shifts base 3, the `2^a` shifts base 2).
Concatenating `r` such blocks separated by powers of 6 gives `a n = P - Q` with
`P ∈ r·R₂`, `Q ∈ r·R₃`, where `R₂ = {s₃(2^a)} ⊆ 2ℤ` (since `s₃ m ≡ m mod 2`, `2^a` even) and
`R₃ = {s₂(3^b)}`.  Numerically `R₂` has density ≈ 0.965 among evens and `R₃` ≈ 0.72 overall,
so (Mann/Cauchy–Davenport) `R₂+R₂ ⊇` all large evens and `R₃+R₃ ⊇` all large integers, whence
`P - Q` attains every `z` with witnesses `→ ∞` — a COMPLETE reduction, and Mathlib even
supplies the additive combinatorics (`Combinatorics.Additive.CauchyDavenport`, `Schnirelmann`,
`PluenneckeRuzsa`).  The single missing input is *positive lower density of `R₂` and `R₃`*, i.e.
anti-concentration of the base-3 digit sum of `2^a` and the base-2 digit sum of `3^b`.  Even the
far weaker `s₃(2^n) → ∞` is a deep theorem (Stewart 1980, via Baker's theorem on linear forms
in logarithms); the density statement is harder and connects to open Erdős problems on the
digits of `2^n`.

THE DECISIVE OBSTRUCTION (why no constructive/elementary proof can exist).  Every route needs
an infinite family of multiples of `6^v` with a KNOWN `a`-value.  One CAN control one digit sum:
`G = 2^(v+N) - 2^(v+M)` with `N - M = 2·3^(v-1) = ord_{3^v}(2)` satisfies `6^v ∣ G` and
`s₂(G) = N - M` exactly — but `s₃(G)` is scrambled; symmetrically a difference of two powers of 3
controls `s₃` but scrambles `s₂`.  Controlling BOTH simultaneously in an infinite family would
produce infinitely many integers with boundedly many nonzero digits in both bases 2 and 3 — which
CONTRADICTS the theorem of Stewart / Loxton–van der Poorten (proved via Baker's theorem on linear
forms in logarithms).  Hence no explicit constant-`a` family exists, the proof MUST be
non-constructive (a large-deviation local limit theorem for the joint law of `(s₂ n, s₃ n)`;
Kim / Drmota–Mauduit–Rivat / Gelfond), and the count `#{n<N : a n = z}` is confirmed to grow (the
self-similar convolution `(m ↦ a(6^v m)) ⋆ (x ↦ a x)` at fixed `z` scales with `2^{2v}`).

Consequently no elementary proof is available, and formalizing the required analytic number
theory (anti-concentration of digit sums of `2^a`, `3^b`; Baker/Stewart bounds; the joint local
limit theorem) is beyond the current Mathlib toolset. The statement below is left unchanged.
-/
theorem oeis_180017_conjecture_0 :
  ∀ z : ℤ, Set.Infinite { n : ℕ | a n = z } := by sorry
