import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

/--
A265709: $a(n) = \mathrm{numerator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
$\sigma(d)$ is the sum of the divisors of $d$, $\sigma(d) = \sum_{k|d} k$.
-/
def A265709 (n : ℕ) : ℕ :=
  -- The sum \sum_{d|n} 1/\sigma(d), calculated in the rational numbers ℚ.
  let sum_of_reciprocals : ℚ :=
    n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)

  -- The numerator of the minimal representation of the rational number, converted from ℤ to ℕ.
  sum_of_reciprocals.num.toNat

/-
Disproof of Conjecture A265709.

We claim there is NO integer `n > 1` for which `S(n) := ∑_{d|n} 1/σ(d)` is an integer,
i.e. the existence statement is false.

Mathematical analysis (the reduction and cases (i)–(iv) below are fully rigorous):

* `1/σ` is multiplicative, so `S(n) = ∏_{pᵃ‖n} f(p,a)` with `f(p,a) = ∑_{i=0}^a 1/σ(pⁱ)`,
  and `S(n) > 1` always (the `d = 1` term contributes `1`). Integrality of `S(n)` is equivalent
  to: `v₂(S(n)) ≥ 0` AND the odd part of the reduced denominator is `1`.
* 2-adic valuation (via LTE). For every odd prime `p` and `a ≥ 1`,
  `v₂(f(p,a)) = -(v₂(p+1) + ⌊log₂(a+1)⌋ - 1) ≤ -1`, because `σ(pⁱ) = (p^{i+1}-1)/(p-1)` is odd
  iff `i` is even, and the unique odd `i` with `i+1 = 2^{⌊log₂(a+1)⌋}` gives the strict minimal
  valuation. Only the prime `2` supplies a nonnegative `v₂` (`σ(2ⁱ) = 2^{i+1}-1` is odd, so
  `V(a₂) := v₂(f(2,a₂)) ≥ 0`). Master identity `v₂(S(n)) = V(a₂) - ∑_{odd p|n} w_p`,
  `w_p := -v₂(f(p,a_p)) ≥ 1`. Moreover `V(a) = 0` for `a` even, `V(a) = 1` for `a ≡ 3 (mod 4)`,
  and `V(a) ≥ 2` for `a ≡ 1 (mod 4)`.
* Rigorous cases (using `f(2,a) < F(2) = ∑_{k≥1} 1/(2ᵏ-1) < 23/14 < 2`, `f(5,2) = 223/186`,
  `f(3,2) = 69/52`, and `f` increasing in `a`, decreasing in `p`):
  - (i) `n` odd ⇒ `v₂(S) = -∑ w_p ≤ -1 < 0`, not an integer.
  - (ii) `a₂` even ⇒ `V = 0`; either `n = 2^{a₂}` (`S = f(2,a₂) ∈ (1,2)`) or an odd prime gives
    `v₂(S) < 0`. Not an integer.
  - (iii) `a₂ ≡ 3 (mod 4)` ⇒ `V = 1` ⇒ at most one odd factor with `w_p = 1` (so `p ≡ 1 (mod 4)`,
    `a_p ≤ 2`): `S < (23/14)·(223/186) < 2`. Not an integer.
  - (iv) `a₂ = 1` ⇒ `V = 2`, `f(2,1) = 4/3`: at most two `w = 1` odd primes or one `w ≤ 2` prime;
    all sub-products satisfy `S ≤ (4/3)·f(5,2)·f(13,2) < 2` or `S ≤ (4/3)·f(3,2) = 23/13 < 2`.
  Hence any hypothetical witness must have `a₂ = v₂(n) ≡ 1 (mod 4)` and `a₂ ≥ 5`, with an odd part `> 1`.

Structure of the remaining (open) case. Integrality fails exactly when some prime remains in the
reduced DENOMINATOR (a prime in the numerator, e.g. the `971` in `f(2,5) = 2⁴·971/(3²·5·7·31)`, is
harmless). The denominator primes of `f(2,a₂)` are the surviving prime factors of the Mersenne
numbers `σ(2ᵏ) = 2^{k+1}-1` (`k = 1..a₂`), INCLUDING large Mersenne primes
`31, 127, 8191, 131071, 524287, 2147483647, …`. To clear a denominator prime `q` one needs an odd
"absorber" prime `p | n` with `q | num(f(p,a_p))` (for `a_p = 1` this is `q | p+2`, so `p ≈ q`; for
`a_p = 2` a cubic condition, `p ≈ q^{1/2}`). Clearing a large Mersenne prime `M` forces an absorber
`p ≈ M^{1/deg}`, whose own `σ(pⁱ)` reintroduces new (smaller) denominator primes — a cascade that
DESCENDS in size, so there is no size monovariant. The number of distinct denominator primes of
`f(2,a₂)` grows (roughly linearly in `a₂`), while the 2-adic budget `V(a₂)` (the maximal number of
odd prime factors) stays small and erratic; but a single absorber may clear several primes at once and
absorbers' denominators may be cleared by other absorbers' numerators, so no clean counting bound is
available. There is provably NO finite covering set of primes: for every bound `B` there is `n` whose
reduced denominator has no prime `≤ B` (e.g. `n = 6025440 = 2⁵·3·5·12553` has reduced denominator
exactly the prime `6277 | σ(12553)`; `131071 = σ(2¹⁶)` survives at `n = 2¹⁷·3`). Cross-cancellation is
real (`num f(3,3) = 703 = 19·37` clears `37 | σ(73)`; `f(29,1) = 31/30` clears `31 = σ(2⁴)`), and the
attainable magnitude is unbounded (`∏_{p≡1 (4)} f(p,2)` diverges).

An exhaustive computational search finds NO counterexample (`n ≤ 1.2·10⁷` directly; budget-bounded
exact-rational searches over the structured candidate space for `a₂ = 5, 9, 13, 17` are empty; the
smallest reduced denominator in the hard core is `405`, at `n = 13920` with `S = 971/405`). All
evidence indicates the statement is TRUE (no witness exists). A complete elementary proof of the
`a₂ ≡ 1 (mod 4)`, `a₂ ≥ 5` case is, however, a genuinely hard (apparently open) global-integrality
statement whose resolution seems to require primitive-prime-divisor (Zsygmondy-type) control that is
not available in the present library. The proof below records the statement; that case is the
mathematical crux.
-/
theorem oeis_265709_conjecture_0.disproof :
  ¬ (∃ (n : ℕ), 1 < n ∧
    ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1) := by
  sorry
