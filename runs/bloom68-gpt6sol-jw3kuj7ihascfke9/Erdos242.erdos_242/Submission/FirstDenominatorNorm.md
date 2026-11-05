# The **first-denominator** norm after the `q₀` failure

**Result:** No proof or disproof of Erdős–Straus was found. `Submission/Spec.lean` is unchanged. `FirstDenominatorNorm.lean` proves the exact first-fiber case split, an exact but *conditional* Type-II congruence reduction, six strictly ordered solutions, two coordinate-parameter counterchecks, and a new **universal negative result**: a natural eligible first denominator constructed from any representation `q=u²+3v²` with **u,v>0** necessarily fails **both complete Type-I and Type-II criteria**. This last theorem is a barrier to one norm-based construction, emphatically **not** a bad prime. The only change to a pre-existing helper is making the already-proved square-plus-product factor/reciprocity lemma public in `EisensteinNormBarrier.lean` so it can be reused here.

## What the new case split does (and does not do)

For a hard prime `p=24k+1` write `q=(p+3)/4=6k+1`. Every ordered first denominator is exactly `x_j=q+j`, `0≤j<6k`, with modulus `a_j=4j+3`. The complete verified conditions are

- **I:** `c>0`, `c | x_j²`, `a_j | 4c+1`;
- **II:** `0<d<x_j`, `d | x_j²`, `a_j | x_j+d`.

`first_denominator_iff_inert_prime_factor` proves in Lean, *without assuming p prime*, that at `j=0` either condition holds iff `q` has a prime factor `2 (mod 3)`; in fact **both** conditions then hold, with that factor serving as `c=d`. Conversely, `first_denominator_fails_iff_split_factors` proves that if this fiber fails, **all** prime factors of `q` are `1 (mod 3)`. Crucially the proof handles **all** divisors of `q²`, not just of `q` (`split_prime_square_divisors_mod_three`).

Since `q` is odd and all its primes split in the Eisenstein integers, it can be represented as `q=u²+3v²`, and hence `p=4u²+12v²−3`. For completeness, an ordinary mathematical proof of the *existence* assertion uses the Euclidean ring `ℤ[ω]`: every odd prime `r≡1 (mod 3)` has a norm `r=N(a+bω)=a²−ab+b²`. A unit rotation makes `b` even; setting `u=a−b/2`, `v=b/2` gives `r=u²+3v²`. The identity

`(u²+3v²)(s²+3t²)=(us−3vt)²+3(ut+vs)²`

then handles products, taking absolute values of the coordinates. **This existence argument is not formalized as a new Lean theorem.** The Lean norm-dependent theorems assume an explicit representation, so no unproved existence or primitivity statement has been smuggled into a formal claim. In particular an arbitrary norm representation does **not** prove the split-factor condition: `25=5²+3·0²` has the inert factor `5`, and both complete types work at `q=25` for `p=97` (`first_norm_alone_does_not_imply_failure`). Also `49` has both the primitive `(u,v)=(1,4)` and nonprimitive `(7,0)` representations; primitivity must not be silently assumed.

`split_first_denominator_good_iff_later_fiber` states the precise remaining task **within** the split-factor branch: find some `0<j<6k` satisfying Type I or II at `x_j`. `good_of_first_denominator_inert_factor` handles the *other* branch with a strictly ordered solution. The Lean theorem `all_good_iff_split_first_denominator_later_cover` proves that **the entire ordered Erdős–Straus statement is equivalent to universally covering the remaining later fibers for split-factor hard primes**. Thus the proposed case split does not, by itself, diminish the hard-prime covering obligation. Expanding the predicates, the norm changes this only to the still-unproved exact requirements

```
∃ j, 0<j<6k, x=u²+3v²+j, a=4j+3,
    (∃ c>0, c|x², a|4c+1)
     or (∃ d, 0<d<x, d|x², a|x+d).
```

Knowing a norm, a residue sign, or the number of divisors does **not** exhibit such a `j,c,d`. Proving it for every prime in this branch would settle the hard-prime case of `CoveringGap.all_good_iff_explicit_hard_cover`.

## New norm-specific obstruction: a guaranteed **bad** candidate

For any norm representation with `u,v>0`, set

```
T = 4v²−1 = (2v−1)(2v+1),       p = (2u)² + 3T.
```

Every odd prime `r|T` sees `p≡(2u)² (mod r)`. As `p` is prime and `T<p`, this square is nonzero; quadratic reciprocity (since `p≡1 (mod 4)`) yields `(r/p)=+1`. Also `(2/p)=+1` for `p≡1 (mod 8)`. Hence **every prime factor of `2^e T` is a residue modulo `p`**. The already proved *full-square-divisor* Jacobi obstruction `PointwiseJacobi.no_types_if_prime_factors_residue` rules out **both** complete criteria at such an `x` whenever it is eligible. The positivity `0<T≤2q−2` allows repeated doubling to select an `e` with `q≤x=2^eT≤2q−2`, so eligibility is **guaranteed**, not assumed. `first_norm_twin_product`, `first_norm_twin_factor_residue`, `dyadic_first_denominator_window`, and `first_norm_forces_eligible_failed_fiber` formally prove the whole implication, including the strict ordered window, without any heuristic inference about individual divisors.

This does **not** rule out the next first denominator or another `j`. It demonstrates that the most direct factors **forced** by the special norm of `q` point in the *wrong* direction. `first_norm_six_twinned_fibers_fail` checks six instances in Lean; each prime also has a different successful fiber:

| prime `p` | `q=u²+3v²`, split factors | norm-forced `T`, bad eligible `x=2^eT` | first successful `j` in finite scan; exact certificate |
| ---: | --- | ---: | --- |
| 193 | `49=1²+3·4²=7²` | `63`, `x=63` | `j=1`, `x=50`, **I** `c=5` |
| 2521 | `631=22²+3·7²` (prime) | `195`, `x=780` | `j=5`, `x=636`, **II** `d=8` (also I `c=477`) |
| 66529 | `16633=85²+3·56²` (prime) | `12543`, `x=25086` | `j=4`, `x=16637`, **I** `c=2179447>x` |
| 18481 | `4621=17²+3·38²` (prime) | `5775`, `x=5775` | `j=4`, `x=4625`, **II** `d=125` (also I `c=185`) |
| 2473 | `619=16²+3·11²` (prime) | `483`, `x=966` | `j=1`, `x=620`, **I** `c=5` |
| 409 | `103=10²+3·1²` (prime) | `3`, `x=192` | `j=1`, `x=104`, **II** `d=1` |

The primalities, q-norm identities, first-fiber failures, displayed Type-I/II certificates, norm-forced bad-fiber failures, and `Good p` (integer **strictly ordered** denominators) are Lean-checked as `first_norm_stress_*` and `first_norm_six_twinned_fibers_fail`. The assertion that each displayed `j` is the *first* success requires enumerating earlier `j` and is **only** checked by the Python audit, not by those Lean theorems. The audit independently constructs complete lists of divisors of `x²` and verifies the resulting strictly ordered fraction identities using `fractions.Fraction`.

## Why even favorable signs and the norm coordinates cannot give a formula

For a Type-II modular parameter `m>0`, write `h=4m−1`. Because `p=4q−3` and `h` is coprime to four, the Lean lemma `first_norm_typeII_modular_iff` proves (provided `3m≤q+d`)

```
h | p+4d    ⇔    h | q+d−3m,
```

but the *separate* necessary condition `d|m²` remains. When `m=v>0`, the inequality is automatic and this equivalence specializes to `first_norm_v_modular_iff`. For `p=2473,q=619,(u,v)=(16,11)`, `h=43` has the needed **negative** Jacobi `(2473/43)=−1` but demands `d≡16 (mod 43)`; the divisors of `11²` are `1,11,121` (residues `1,11,35`), none matches. This mismatch is proved in Lean by `first_norm_v_2473_sign_without_exact_divisor`. For the more demanding prime `66529`, **both** coordinate parameters `m=u=85` and `m=v=56` fail for *every* `d|m²`, with no size truncation: `h=339` has positive sign; `h=223` has the *admissible negative sign* but needs `d≡37 (mod 223)`, missing among divisors of `56²=2⁶·7²`. `first_norm_66529_coordinate_parameters_fail` proves these assertions in Lean. This prime nonetheless succeeds at `x=16637` via full Type I and at `m=10,d=50` via full Type II (the latter was already certified in `CoveringGap.lean`). A failed norm-coordinate parameter is **not** a bad prime.

More fundamentally, for a **primitive** representation with `q≡1 (mod 3)`, `gcd(u,q)=gcd(v,q)=1` (`primitive_first_norm_coordinates_coprime`). Thus any nontrivial `u` or `v` **cannot even divide `q²`** (`primitive_first_norm_coordinates_not_square_divisors`). The norm decomposition is *additive*, not an allocation of the required square divisor. At a shifted `x` the factorization of `x²` changes completely, and the exact target residues must be checked anew.

As a particularly strong **finite, Python-only** check against a coordinate-*multiple* formula, at `p=66529` *all* 196 eligible first denominators divisible by `u=85` and *all* 297 divisible by `v=56` fail **both** full types. The Python script factors each `x`, lists **all** divisors of `x²`, and tests both exact residues, not just characters or divisors of `x`. This is not a Lean theorem, not an exclusion of other denominator choices, and not an all-prime statement; `x=16637`, not divisible by 85 or 56, works.

**Remaining obstruction:** one must prove for *every* prime in the norm/split branch that some **other**, potentially unrelated first denominator `x=q+j` has a divisor of `x²` in one of the two *specific* target classes, or show a prime that fails both types at **every** such `j`. The new universal norm identity instead supplies an entire natural family of impossible fibers, and the negative-sign coordinate tests demonstrably fail to select the required divisor. There is currently no universal formula or descent, and no counterexample prime, from this case split.

**Checks:** `lake env lean Submission/FirstDenominatorNorm.lean`; `lake build Submission.FirstDenominatorNorm`; `python3 Submission/FirstDenominatorNormAudit.py`. The old `Spec.lean` SHA-256 remained `9f079b4c04f5596d6f13a848eb274e32a2235d4fbd9818b0ed22800512ba8c5f` throughout. No new axiom, `sorry`, `native_decide`, or edit to that spec is used.
