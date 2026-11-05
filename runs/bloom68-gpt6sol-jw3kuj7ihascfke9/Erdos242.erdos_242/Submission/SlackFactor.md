# Positive-slack factorization for the hard prime Erdős–Straus problem

**Status: the universal construction is still missing.** The sorry-free `Submission/SlackFactor.lean` formalizes an exact factor reformulation, identifies its complete Type-I/II split, and proves two substantive obstructions to proposed formulas for `A`. It neither asserts that a valid `A` exists for every hard prime nor imports or changes `Submission/Spec.lean`.

## Exact criterion, including strict order

For a prime `p≡1 (mod 24)`, the following are equivalent (`good_iff_exists_slack_factors`, `slack_factors_iff_ordered`): an ordered solution `x<y<z` exists, and **some** positive integer `A` has factors `a,b` satisfying

```text
a≡b≡3 (mod 4),   0<a<b,   a<p,   ab=p²+4A,
A | ((p+a)(p+b))/16,       4A<p(p+a).                 (F)
```

Recover `x=(p+a)/4`, `y=(p+b)/4`, `z=p·xy/A`. The divisibility in (F) is meaningful because `16 | (p+a)(p+b)`; it is equivalent to `A|xy`. The final condition is **necessary**: it says precisely `A<px`, or `y<z`. The bound `a<p` says `x<p/2`, while `a<b` says `x<y`. Conversely, the proven prime classification gives `p|z`; writing `z=pt` and clearing denominators yields

```text
4xyt=xy+pt(x+y),   hence t|xy,
A=xy/t=4xy-p(x+y)>0,   ab=p²+4A.
```

This establishes (F) as an *exact equivalent question*, not a new existence argument. Every valid `A` satisfies `2A<p²` (`ordered_slack_size_bound`); therefore there is a finite, but `p`-dependent, exhaustive search (`good_iff_finite_slack_factors`). Success for every prime is **unproved**.

**Ordering cannot be omitted.** For `p=73`, `A=32193`, `(a,b)=(11,12191)` and `(x,y)=(21,3066)`, one has `ab=p²+4A` and `xy=2A`, but `z=73·2=146<y`. Thus factorization, factor congruences, `a<b` with `a<p`, and `A|xy` do **not** assert the particular ordered triple `x<y<z`. `factor_and_divisibility_do_not_force_order` checks the integers in Lean.

## What `A` actually encodes: both *full* types

Put `a=4x-p`, so `ay=px+A`. Since `0<a<p`, primality gives `p∤a`. The theorem `slack_prime_dvd_iff_middle` proves `p|A ↔ p|y` at the **specified** first and middle denominators.

* If `p∤A`, then `A|xy` and `ay=px+A` imply `A|p x²`, hence `A|x²`. Set `c=x²/A`. The exact shifted-square equivalence `a|p²+4A ↔ a|4c+1` (the reverse direction cancels the coprime factor `4A`) gives the **full Type I** certificate `c|x²`, not just `c|x`. This is `ordered_slack_typeI_data`; it proves `A·c=x²` with the *same* first denominator `x`.
* If `p|A`, write `A=pd`; then `p|y`, say `y=pm`, and `am=x+d`. The conditions `A<px` and `A|xy` give `0<d<x` and `d|xm`. Multiplying `am=x+d` by `x` shows `d|x²`; also `a|x+d`. This is exactly **full Type II**, formally `ordered_slack_typeII_data`, again at the same `x` and with `A=pd`.

Conversely, the ordered triples constructed from the full Type-I and Type-II criteria in `Classification.lean` have respectively `A=x²/c` and `A=pd` (with the corresponding `y=(px+A)/a` and `y=p(x+d)/a`). Thus working solely with `p∤A` would silently discard Type II. Type I even has `A|x²<p²/4`; the weaker common size bound `A<p²/2` covers both types.

## A genuine obstruction to `p−1` divisors and square/norm choices

At any hard prime a valid `A` must satisfy

```text
p|A    or    (A/p) = −1,                                  (C)
```

where `(A/p)` is the Legendre symbol (the corresponding Jacobi statement is `ordered_slack_jacobi_or_prime`). For `p∤A`, Type I has `Ac=x²`; the previously formalized `typeI_cofactor_jacobi_neg_one` gives `(c/p)=−1`, while `(x²/p)=1` because `0<x<p`. Thus `(A/p)=−1`. This character condition is *necessary, not sufficient*: for `p=193,A=5`, `(5/193)=−1` and `p²+20=3²·41·101` has **two** eligible factor pairs `(a,b)=(3,12423),(123,303)`, but in both cases `xy≡1 (mod 5)`. No valid `A=5` follows (`SlackFactorAudit.py` checks both pairs).

Every positive divisor `A` of `p−1` has `(A/p)=+1`: for an odd prime `q|p−1`, `p≡1 (mod q)` and reciprocity with `p≡1 (mod 4)` give `(q/p)=(p/q)=+1`; for `q=2` use `p≡1 (mod 8)`, then multiply the prime-factor signs. Hence **no `A|p−1` can work for any hard prime**, not just the five examples (`hard_minus_one_divisor_jacobi_one`, `ordered_slack_not_dvd_pminusone`, `hard_slack_factors_not_dvd_pminusone`). This excludes the divisor choice, *not every conceivable formula involving `p−1`*.

Similarly, **no square `A=s²` works at a hard prime** (`hard_no_square_slack`): if `p∤s`, its symbol is `+1`, and if `p|s`, then `A≥p²` violates the strict size bound. Equivalently, for `p∤s`, the primitive Gaussian norm `p²+(2s)²` has no prime divisor `3 (mod 4)` at all. In particular the Gaussian representation `p=u²+v²` cannot make `A=u²` or `A=v²` work. More generally, the earlier `GaussianNormBarrier.gaussian_coordinate_factors_residue` proves every prime dividing `uv` is a residue modulo `p`; together with (C) and Jacobi multiplicativity, this also excludes positive `A` supported **only** on primes dividing `uv`. This last corollary is a paper deduction from two Lean-proved lemmas, not a separately named theorem in `SlackFactor.lean`. It does **not** exclude other functions of `u,v` involving external prime factors.

The obstruction is unbounded in a precise sense (`hard_primes_escape_bounded_slack`, `hard_primes_escape_bounded_slack_factors`): for every *fixed* `B` and arbitrarily large hard primes, **all** `A≤B` fail. Choose by Dirichlet a prime `p≡1 (mod 24·B!)`; then every `1≤A≤B` divides `B!`, hence divides `p−1` and is impossible by (C). This proves that a successful all-prime formula, if it exists, must be unbounded. It does **not** construct such a formula or imply any one hard prime is insoluble.

## Integer-only stress tests

`python3 Submission/SlackFactorAudit.py` tests primality by trial division, enumerates **every** possible `3 (mod 4)` smaller factor up to `⌊√(p²+4A)⌋` for *each* `A` below the listed minimum, and checks the exact integer product, divisibility, strict order and cleared-denominator equation at the first success. The positive factor certificates are also kernel-checked as `slack_factors_*` in Lean; the exhaustive **minimality** statements are checked by the script, **not** formalized in Lean. These are only five primes, not evidence of pointwise coverage for all primes.

| prime `p` | minimal `A` | `a,b` | ordered `(x,y,z)` |
|---:|---:|---:|---:|
| 73 | 7 | 11, 487 | 21, 140, 30660 |
| 193 | 10 | 7, 5327 | 50, 1380, 1331700 |
| 2521 | 76 | 1583, 4015 | 1026, 1634, 55610739 |
| 66529 | 19 | 6811, 649847 | 18335, 179094, 11497921660590 |
| 18481 | 38 | 5079, 67247 | 5890, 21432, 61393142760 |

## Factor structure and the precise gap

For fixed `p,A`, `ab=p²+4A` is a split affine hyperbola; its integral points are the finitely many factor pairs of that integer. Because it is `1 (mod 4)`, a pair `a,b≡3 (mod 4)` needs an eligible divisor containing an odd number of primes `3 (mod 4)` (counted with multiplicity). Even forcing such a prime factor, or merely forcing the negative character (C), does not force `A|((p+a)(p+b))/16` or the ordering bound. The `p=193,A=5` calculation exhibits that exact failure. No factorization of `p−1`, primitive sum-of-squares representation, fixed-bound search, or descent through these fibers presently proves that for **each** `p=24k+1` there is a good `A`; equivalently, by `Classification.good_iff_explicit_divisors`, for **some** eligible `x=6k+1+j` (`0≤j<6k`) there is a full Type-I cofactor `c|x²`, `4j+3|4c+1`, **or** a full Type-II divisor `0<d<x`, `d|x²`, `4j+3|x+d`. This missing **pointwise** existence assertion is exactly the global Erdős–Straus gap. An all-prime disproof would require a certified hard prime and failure of *both* conditions for *every* such `x`; no example here is such a prime.

Verification: `lake env lean Submission/SlackFactor.lean`, `lake build Submission.SlackFactor`, and `python3 Submission/SlackFactorAudit.py`. Auditing the new equivalence, character, no-`p−1` and Dirichlet theorems using `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`, not `sorryAx`; `Submission/Spec.lean` is unchanged.
