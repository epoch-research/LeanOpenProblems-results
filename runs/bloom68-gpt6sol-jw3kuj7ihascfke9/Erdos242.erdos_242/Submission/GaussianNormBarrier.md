# Gaussian norms do not supply the missing Erdős–Straus divisor

**Status:** `GaussianNormBarrier.lean` proves the norm-coordinate and
first-denominator statements below, without importing or editing
`Spec.lean`. They are **pointwise necessary restrictions, not a proof or
counterexample** to Erdős–Straus. The elementary dyadic lemma near the end
has a complete ordinary proof here; it is not asserted as a Lean theorem.

## A universal Gaussian-coordinate obstruction

Let `p` be prime, `p ≡ 1 (mod 8)`, and `p = u² + v²` with `u,v>0`.
For **every prime factor** `r | uv`,

    (r/p) = +1.                                               (1)

For odd `r|u`, first `r∤v`: otherwise `r|p`, and primality would give
`r=p`, impossible since `r≤u<p`. Therefore `p≡v² (mod r)` is a
*nonzero* square, and reciprocity (using `p≡1 mod 4`) gives
`(r/p)=(p/r)=+1`. Interchange `u,v` for `r|v`. For `r=2`, use
`p≡1 (mod 8)`, so `(2/p)=+1`. This proof also works when the Gaussian
coordinates have repeated or composite factors: **each individual prime
factor**, not just their overall Jacobi products, is a residue. Fermat's
two-squares theorem, already in Mathlib, gives such positive `u,v` for
*every* hard prime `p=24k+1` (`hard_prime_has_gaussian_coordinates` and
`gaussian_coordinate_factors_residue`).

For a candidate first denominator `p<4x`, `x<p`, the full Type-I and
Type-II criteria respectively require

    c>0, c|x², 4x−p | 4c+1;
    0<d<x, d|x², 4x−p | x+d.                               (2)

`PointwiseJacobi.hard_types_need_large_nonresidue` says that either
criterion for a hard prime forces a prime `r≥5`, `r|x`, `(r/p)=−1`.
By (1), this `r` **cannot divide `uv`**. The Lean theorems
`hard_gaussian_solution_needs_external_prime` and
`gaussian_supported_candidate_no_types` formalize these implications:
for all `e≥0` and all eligible `x` with `x | (uv)^e`, **both full
criteria fail at that x**. `hard_prime_gaussian_supported_fibers_fail`
combines this with the existence of Gaussian coordinates at *every*
hard prime. This is a universal obstruction to constructing a first
denominator out of Gaussian-coordinate prime factors, not an obstruction
to first denominators containing other primes.

An especially natural norm-derived choice is `x=uv`. Because
`2uv≤u²+v²=p`, it is below `p/2`; if the additional balance condition
`p<4uv` holds, it lies in the entire ordered candidate range. Yet
**both** conditions (2) fail at that particular `x`
(`gaussian_product_no_types`). This is a genuinely *pointwise* negative
result: a norm identity can put a candidate in the correct interval
without placing **any** divisor in the required residue class.

## Exact stress tests (failure at one fiber, success at another)

The three norm-product fiber failures below are proved in Lean, including
primality. Type-I/II certificates, strict ordered-solvability and exact
rational identities for **all three** primes are also proved in the new
file (`norm_escape_193_*`, `norm_escape_2521_*`, `test_6553_*`).
All displayed denominators are strictly ordered.

| prime `p=u²+v²` | Gaussian `x=uv`, `4x−p`; both types fail | different working `(x,a,c or d)` | ordered denominators `(x,y,z)` |
|---|---|---|---|
| `193=7²+12²` | `(84,143)` | `(50,7,c=5)` | `(50,1450,27985)` |
| `2521=35²+36²` | `(1260,2519)` | `(636,23,d=8)` | `(636,70588,5611746)` |
| `6553=37²+72²` | `(2664,4103)` | `(1639,3,d=11)` | `(1639,3604150,537018350)` |

At `p=193`, `x₀=(p+3)/4=49=7²` has no nonresidue prime factor,
so **both** types fail there (Lean: `first_candidate_193_fails`),
whereas the outside Gaussian-coordinate prime `5` makes `c=5|50²`
and `7|4·5+1` work at `x=50`. At `p=2521`, `x₀=631≡1 (mod 3)`
is prime and fails (Lean: `first_candidate_2521_fails`);
`x=636=2²·3·53` has the external nonresidue `53`, and `8|636²`,
`23|636+8` gives Type II (also at `x=638,d=44` in
`CoveringGap.lean`). At `p=6553`, **the very first** candidate
`x₀=1639=11·149` already works with both types (Lean:
`test_6553_typeI`, `test_6553_typeII`): `11|1639²` and
`3|1639+11` (indeed `3|4·11+1`). Here
`(11/6553)=−1` since `6553≡8 (mod 11)`, and `11∤37·72`.
This explains why failure of a Gaussian-product candidate, or of the
first candidate at a different prime, never establishes a bad prime.

## A complementary universal lemma: the nonresidue sieve can be passed

**Dyadic-window lemma (ordinary proof).** For **every** prime
`p≡1 (mod 8)` there is some integer `x` with

    p < 4x,           2x < p,           (x/p)=−1.           (3)

In particular for every hard prime **at least one** eligible `x` has
a nonresidue prime factor, necessarily at least `5`. To prove this,
choose any nonsquare `n` modulo `p`, with `1≤n<p`. As `(-1/p)=1`,
replace `n` by `p−n` if necessary to obtain `0<n<p/2`, still a
nonresidue. Let `e` be maximal with `2^e n<p/2`, and put `x=2^e n`.
Then `2x≥p/2`, while `x<p/2`; since `p` is odd and `4x` is an
integer multiple of four, equality `4x=p` is impossible. Thus
`p<4x`. Finally `(2/p)=1` gives `(x/p)=(2/p)^e(n/p)=−1`.
A negative product of Legendre signs has a negative prime factor;
`(2/p)=(3/p)=+1` if `p≡1 (mod 24)`. The maximum `e` exists because
`n>0` and powers of two grow without bound.

The lemma **does not** provide a suitable divisor `c` or `d` in (2):
the required classes are respectively `c≡−4⁻¹` and `d≡−x`
modulo `4x−p`, not merely the negative-character half of the units.
For an illustrative *exact finite check*, take the least nonresidue
primes `r=5,11,5` for `p=193,2521,6553` respectively; doubling
until (3) holds gives `(x,4x−p)=(80,127),(704,295),(2560,3687)`.
In all three cases `x=2^e r` and **every** divisor of `x²` has the form
`2^i r^j`, `0≤i≤2e`, `0≤j≤2`. Reducing these respectively `27`, `39`,
`57` integers modulo `a=4x−p` misses **both** required residues:

| `(p,r,e)` | `a` | Type-I target `−4⁻¹ mod a` | Type-II target `−x mod a` |
|---|---:|---:|---:|
| `(193,5,4)` | 127 | 95 | 47 |
| `(2521,11,6)` | 295 | 221 | 181 |
| `(6553,5,9)` | 3687 | 2765 | 1127 |

The exhaustive elementary check is reproduced by this short integer-only
certificate (it even excludes the Type-II target **without** requiring
`d<x`):

```python
for p,r,e in [(193,5,4), (2521,11,6), (6553,5,9)]:
    x, a = (2**e)*r, 4*(2**e)*r-p
    residues = {(2**i * r**j) % a
                for i in range(2*e+1) for j in range(3)}
    assert (-pow(4,-1,a)) % a not in residues
    assert (-x) % a not in residues
```

Thus neither full type works at **each of these three x**, despite
`(x/p)=−1`; the primes have the different positive solutions in the
earlier table. These finite checks are not used in either universal
Lean theorem.

## Exact missing implication

`CoveringGap.all_good_iff_explicit_hard_cover` reduces a universal
proof to **every** hard prime `p=24k+1` admitting **some**
`x_j=6k+1+j`, `0≤j<6k`, with `a_j=4j+3` and **either** a positive
`c|x_j²` with `a_j|4c+1` **or** `0<d<x_j`, `d|x_j²`,
`a_j|x_j+d`. An insoluble prime would require proving failure of
**both** alternatives at **all** such `j`. Neither Fermat's norm
identity, the residue condition (1), the guaranteed nonresidue
candidate (3), nor a finite set of examples supplies this implication
or its negation. In particular nothing here constructs integer
Egyptian-fraction denominators for every hard prime; the
Erdős–Straus conjecture remains unresolved.
