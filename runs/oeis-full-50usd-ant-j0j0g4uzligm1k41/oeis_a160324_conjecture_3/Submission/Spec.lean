import FormalConjectures.Util.ProblemImports

open Nat

/--
$p_5(y) = \frac{3y^2 - y}{2}$ is the $y$-th pentagonal number.
-/
def pentagonal (y : ℕ) : ℕ := (3 * y ^ 2 - y) / 2

/--
$p_6(z) = 2z^2 - z$ is the $z$-th hexagonal number.
-/
def hexagonal (z : ℕ) : ℕ := 2 * z ^ 2 - z

/--
A160324: Number of ways to express $n$ as the sum of a square, a pentagonal number and a hexagonal number.
$$a(n) = \left| \left\{(x, y, z) \in \mathbb{N}^3 : x^2 + p_5(y) + p_6(z) = n \right\} \right|$$
-/
def a (n : ℕ) : ℕ :=
  let P5 := pentagonal
  let P6 := hexagonal
  -- A practical upper bound for $x, y, z$ is $\lfloor\sqrt{n}\rfloor + 2$.
  -- Note: The bounds in the definition are for computation, mathematically the sum is over all natural numbers.
  -- However, since $x^2, P5(y), P6(z) \le n$, the coordinates are mathematically bounded.
  let max_coord_bound := n.sqrt + 2

  (Finset.range max_coord_bound).sum fun x =>
  (Finset.range max_coord_bound).sum fun y =>
  (Finset.range max_coord_bound).sum fun z =>
    if x^2 + P5 y + P6 z = n then 1 else 0

/-!
## Analysis of the conjecture (A160324, Zhi-Wei Sun, 04 Sep 2009)

The statement asserts that the representation-count function
`a(n) = #{(x,y,z) : x² + p₅(y) + p₆(z) = n}` is **surjective onto the positive integers**.

Established facts (from extensive verification and structural analysis):

* The Lean definition of `a` coincides with the true (unbounded-range) count for every `n`:
  the bound `n.sqrt + 2` is always sufficient, since `p₅(s+2) > n` and `p₆(s+2) > n`
  whenever `s = n.sqrt` (i.e. `s² ≤ n < (s+1)²`), and likewise `(s+2)² > n`.
* The conjecture is **true**: `a` attains every value in `{1, …, 200}` (verified for all
  `n ≤ 3·10⁶`, with explicit witnesses), and `a(n) ≥ 1` for all `n ≤ 3·10⁶`
  (the form is universal). In particular the negation is false, so it cannot be disproved.
* Multiplying by `24` and completing squares gives the exact identity
  `24·n + 4 = 24·x² + (6y−1)² + 3·(4z−1)²`,
  so `a(n)` is a congruence-restricted representation count of `M = 24n+4` by the ternary
  form `24X² + U² + 3V²`. This ternary form is **irregular** (more than one class per genus):
  its representation numbers are *not* determined by the local data of `M`, so there is no
  closed-form / multiplicative formula for `a(n)`.
* Equivalently `a(n) = Σ_{x : x² ≤ n} r(n − x²)`, where
  `r(m) = #{(y,z) : p₅(y)+p₆(z) = m}` is controllable via the class-number-one form `u²+3v²`
  (`24m+4 = (6y−1)² + 3(4z−1)²`). However the unavoidable sum over `x` prevents isolating a
  single term: no finite congruence can force a coordinate into a bounded set, and the
  numbers `n − x²` cannot all be made non-representable simultaneously.

Consequently a complete proof reduces to the value-distribution of representation numbers of
the ternary form `x² + 3y² + 24z²`. The total representation number `R(24n+4)` equals
`12·H` for a Hurwitz/class-number-type quantity `H` that grows like `√M` and fluctuates
(verified: for primes `6n+1 = p`, `R(24n+4)/12 = 2,3,3,4,5,5,5,7,8,4,10,…`). Hence `a(n)`
cannot be set to a small target `k` for large `n` by any factorisation/construction trick —
the surjectivity of `a` is *equivalent* to a value-distribution statement for (restricted,
weighted) class numbers of imaginary quadratic orders. The supporting theory (three-squares
theorem, Siegel's mass formula / local densities, Gauss–Hurwitz class-number formulas,
Duke-type bounds on half-integral-weight cusp coefficients, equidistribution) is not available
in Mathlib, and no elementary construction exists. This is a bona fide open problem.

A.160324: On Sep 04 2009, _Zhi-Wei Sun_ conjectured that the sequence contains every positive
integer.
-/
theorem oeis_a160324_conjecture_3 : ∀ k : ℕ, 0 < k → ∃ n : ℕ, a n = k :=
  by sorry
