# The `A²+24B²` norm: proof, exact factor criterion, and stress tests

**Outcome:** The norm representation is valid for every prime `p≡1 (mod 24)`, but it does not yet yield a universally integral, strictly ordered decomposition of `4/p`. The exact norm-factor construction and the finite stress obstructions below are checked in `Norm24.lean` (which does not import or edit `Spec.lean`). The reduced-form and character arguments in this note are ordinary proofs, **not** claimed as Lean theorems. `NormDiagnostics.md` previously stated a different class-group proof of the norm representation; the discriminant-`−96` verification here isolates precisely the new proposed coordinate formula.

## Why the representation is universal

For `p>3` prime, `p≡1 (mod 24)` **if and only if** there are positive integers `A,B` with `p=A²+24B²`. The easy direction: `A` is odd and not divisible by 3 (otherwise `p` would be even or divisible by 3), so `A²≡1 (mod 24)`. Neither coordinate can be zero for a prime `p>3`.

For the converse use the standard reduction theorem for primitive positive definite binary quadratic forms. Because `p≡1 (mod 24)`, quadratic reciprocity gives `(−6/p)=1`. Choose `t` with `t²≡−6 (mod p)` and put `b=4t`, `c=(b²+96)/(4p)`. Then `[p,b,c]` is an **integral primitive** positive definite form of discriminant `−96`, representing `p` at `(1,0)`. Integrality follows from `b²+96=16(t²+6)`; primitivity holds because `p∤b` (as `p∤6`). Reduction and integral equivalence preserve represented integers. Enumeration of the primitive reduced forms of discriminant `−96` gives exactly

```
[1,0,24],   [3,0,8],   [4,4,7],   [5,2,5].
```

The value of `[3,0,8]` is `0` or `2 (mod 3)`, never `1`. Every **odd** value of `[4,4,7]` is `7 (mod 8)` (the second variable must be odd). Every **odd** value of `[5,2,5]` is `5 (mod 8)` (exactly one variable must be odd). Since `p≡1 (mod 24)`, only `[1,0,24]` can represent it: `p=A²+24B²`. Here `B>0` because a prime is not a square. (Equivalently, the reduced forms of discriminant `−24` are `[1,0,6]` and `[2,0,3]`; the latter cannot take values `1 (mod 3)`. Then modulo 8 forces the second coordinate of `A²+6C²` even.) This is an existence proof for the coordinates, **not** a divisor-covering proof.

For an independent finite check, enumeration gives 267 primes `1 (mod 24)` up to 20,000, and 9,732 up to 1,000,000; every one has such a representation. These finite counts do not establish the theorem; the reduced-form argument does.

## A precisely conditional integral norm-factor formula

Write `p=A²+24B²`. Pick `m,d>0`, set `h=4m−1`, and **assume** `h|A`, `d|m²` and `4d<p`. Since `gcd(h,4)=1`, the norm gives the exact equivalence

```
h | p+4d    ⟺    h | 6B²+d.                                 (★)
```

Indeed `p+4d=A²+4(6B²+d)` and `h|A²`; cancellation of 4 proves the forward implication, and multiplication by 4 proves the reverse. Under the additional divisibility in (★), set

```
x=(pm+d)/h,    u=mx/d,    y=pm,    z=pu.
```

The proved `good_of_shifted_offset` shows these quotients are integers, `1≤x<y<z`, and `4/p=1/x+1/y+1/z` **at the given prime**, not merely asymptotically. This specialization and the iff in (★) are Lean theorems `norm24_good_of_factor` and `norm24_factor_modular_iff`. But **the norm alone forces neither `h|6B²+d` nor a suitable divisor `d|m²`**. Choosing `h=A` is permissible only when `A≡3 (mod 4)` and `A≥3`, with `m=(A+1)/4`; choosing a factor of `A` allows other `h`.

There is no candidate at `x=AB` either: `p−4AB=(A−2B)²+20B²>0` for `B>0` (`norm24_product_below_window`), so this coordinate product is always *below* the required ordered first-denominator interval. The alternative Type-I shifted-square formulation in `EuclideanExchange.typeI_slack_iff_square_shift` still requires an **actual** `r|x²` and `4x−p|p²+4r`; the norm identity alone does not provide either divisibility. In particular a square `r` cannot work: `p²+4r` is then a primitive sum of two squares and has no divisor `3 (mod 4)`, while `4x−p≡3 (mod 4)` (or use `SlackFactor.square_shift_jacobi_negative`). Nonsquare complementary divisors and the full Type-I branch remain available.

## Three mandatory stress tests, including the full square-divisor condition

| `p=A²+24B²` | Proposed `h=A` | Exact `d|m²` failure / successful alternative |
| --- | --- | --- |
| `97=1²+24·2²` | `A=1` cannot equal `4m−1` for `m>0` | The prime succeeds at `x=25`, `a=3`, `d=5`: `(x,y,z)=(25,970,4850)`. |
| `1249=35²+24·1²` | `h=35`, `m=9` | (★) requires `d≡29 (mod 35)`; divisors of `81` are `1,3,9,27,81`, none suitable. The **proper factor** `h=7|35` works with `m=2,d=1`: `(357,2498,891786)`; also `x=315,d=15` meets the full Type-II criterion. |
| `2521=11²+24·10²` | `h=11`, `m=3` | (★) requires `d≡5 (mod 11)`; divisors of `9` are `1,3,9`, none suitable. Since `A=11` is prime, **no factor `h=4m−1|A` works at all**. A different modulus `h=87`, `m=22,d=44|22²` works, giving `(638,55462,804199)`. |

The two **negative** `h=A` assertions, the complete norm-factor exclusion at `2521`, prime norms, and positive ordered-solvability assertions are Lean-checked in `norm24_no_A_axis_1249`, `norm24_no_A_axis_2521`, `norm24_no_factor_axis_2521`, and `norm24_stress_*` (the `2521` witness is imported from `CoveringGap.lean`). The exact triples above also pass integer-quotient and rational-identity checks. The `1249` Type-II witness at `x=315` is separately checked in `norm24_1249_first_multiple`. A failed modulus is emphatically **not** an Erdős–Straus counterexample.

For a finer character test, if a prime `r` divides `B`, then `p≡A² (mod r)`; primality makes the square nonzero, so reciprocity (`p≡1 (mod 4)`) shows `(r/p)=+1` for odd `r`, and `(2/p)=+1`. If an odd prime `r` divides `A`, then `p≡24B² (mod r)` with `r∤B`, whence `(r/p)=(6/r)`, which can be **−1**. Thus `11|A` at `2521` and `7|A` at `1249` really do provide nonresidue factors, but even a favorable quadratic-character sign does **not** put any of `1,3,9` into residue `5 (mod 11)`, or any divisor of `81` into residue `29 (mod 35)`. Conversely `A=1` at `97` provides no such factor at all. This is another reason the norm cannot automatically be promoted to either exact Type-I or Type-II divisor.

## The missing universal implication

`CoveringGap.all_good_iff_explicit_hard_cover` requires, for **each** prime `p=24k+1`, at **some** `0≤j<6k`, writing `x=6k+1+j` and `a=4j+3`, either

```
(I)  ∃ c>0, c|x² and a|4c+1;
(II) ∃ 0<d<x, d|x² and a|x+d.
```

In fact, the tempting stronger claim that *every* hard prime admits a norm-factor witness `h=4m−1|A`, `d|m²`, `4d<p`, `h|6B²+d` is **false already at `2521`**, by the Lean theorem above. A valid all-prime proof must allow other Type-II moduli or full Type I: failure of this restricted subfamily does not rule out either, as the independent successful modulus `87` at `2521` shows. The norm representation, reciprocity and class number establish neither the required exact residue for some eligible `x` nor a counterexample excluding **both** full types at **every** `x`. No universal ordered formula in `A,B`, and no proof of the theorem in `Spec.lean`, follows from this analysis.
