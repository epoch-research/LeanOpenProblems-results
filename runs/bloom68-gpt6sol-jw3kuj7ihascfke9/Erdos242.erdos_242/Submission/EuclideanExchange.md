# Euclidean-slack exchange for the ordered Erdős–Straus equation (partial)

**Status.** `EuclideanExchange.lean` is a sorry-free proof importing
`Classification.lean`, not `Spec.lean`. It constructs solutions on a selected
infinite prime progression and checks explicit hard-prime examples. It neither
proves an ordered decomposition for every `p≡1 (mod 24)` nor produces an
insoluble prime. No changes to `Spec.lean` were made.

## A complete alternative for the Type-I branch at a fixed first denominator

Let `p>2` be prime, `p≡1 (mod 4)`, and `p/4<x<p/2`. Set `a=4x−p`, so
`0<a<p`, `a≡3 (mod 4)` and `gcd(a,x)=1`. If `c*r=x²` with positive integers
`c,r`, the **Euclidean-slack equivalence** is

    a | (4c+1)    iff    a | (p²+4r).                            (1)

Indeed the *exact* identity

    4r(4c+1) = (4x)²+4r = a(a+2p)+(p²+4r)                     (2)

proves the forward direction. Since `r|x²`, the assumptions on prime `p`
ensure `gcd(a,4r)=1`: any prime dividing both `a` and `x` would divide `p`,
contrary to `0<x<p`, and `a` is odd. Cancel `4r` in (2) for the reverse
direction. This is formalized by `typeI_slack_iff_square_shift` (and the
forward direction requires no primality). Thus the Type-I option is exactly
the existence of some **divisor `r|x²` in the precise residue class**
`p²+4r≡0 (mod a)`; it is not guaranteed just by a character sign or by
having many divisors. `good_of_typeI_square_shift` formally converts such an
`r` into a positive strictly increasing decomposition, via `c=x²/r`:

    x,    y=(px+r)/a,    z=(px+p²c)/a.                          (3)

Integrality, order and `4/p=1/x+1/y+1/z` follow from the checked full
Type-I construction in `Classification.lean`. This explicitly retains the
**full `c|x²` branch**, not merely `c|x`.

## Complementary-divisor exchange and its exact limitation

Suppose `a|4c+1` and `c*r=x²`, and assume `p>0`. The identity (2) and
`p²−1+1=p²` imply the exact equivalence

    a | (4r+1)    iff    a | (p²−1).                            (4)

This is `typeI_complement_iff_square_one`, proved without assuming that `p`
is prime. When `p²≡1 (mod a)`, **both** `c` and the complementary divisor
`r` satisfy the Type-I target, and (3) gives two ordered decompositions:

    (x, (px+r)/a, (px+p²c)/a),
    (x, (px+c)/a, (px+p²r)/a).                                  (5)

The Lean theorem `typeI_square_one_exchange` constructs the second
certificate. Importantly, (4) only exchanges a certificate **already
found**; `p²≡1 (mod a)` alone does not put any divisor into the requisite
class. Further, the exchange applies only at moduli dividing `p²−1`, not at
all candidate first denominators.

Here is an *infinite, but selected*, nontrivial-root family. For `t≥0`, let

    p=54120t+12409,  q=330t+76,  x=41q=(p+55)/4,
    a=55,  c=41,  r=41q²=x²/c.

Then `p≡1 (mod 24)`, `p≡34 (mod 55)` and `34²≡1 (mod 55)`, even though
`34≠±1 (mod 55)`. Since `4c+1=165=3·55`, both `c` and `r` hit the target.
Set `m=(p+q)/55=990t+227` and `m'=(pq+1)/55` (both are integers). The two
**explicit ordered** identities are

    4/p = 1/(41q) + 1/(41qm) + 1/(41pm),
    4/p = 1/(41q) + 1/(41m') + 1/(41pqm').                    (6)

For the first one, `p+q=55m` makes the numerator after combining the three
fractions equal to `m(p+55)=4xm`; the second uses `pq+1=55m'` similarly.
Strict order follows from `p>q`, `m>1`, `p>55` and `pq>1`. These
claims about *all* `t` follow also from `root55_progression_two_certificates`
and `good_of_typeI`; the explicit expressions in (6) follow from (3).
`gcd(12409,54120)=1`, so Dirichlet gives arbitrarily large prime members;
`infinitely_many_root55_exchange_primes` proves this in Lean. This does
**not** say that arbitrary hard primes lie in this one progression.

The prime `p=66529` is the member `t=1`; `q=406`, `x=16646`, `a=55`,
`r=6758276`. Neither `55|p−1` nor `55|p+1`. The two ordered triples are

    (16646, 20258182, 3319597513),
    (16646, 20135305, 543870172776070).

`test_66529_nontrivial_root` checks primality, both factor congruences, the
absence of `p≡±1 (mod 55)`, and both exact rational identities.

## Why this does not prove the conjecture: a small certified limitation

Even the prime `193` is **not covered by any Type-I certificate satisfying
the extra condition `a|p²−1`**. Indeed

    193²−1=37248=2⁷·3·97.

An eligible `a=4x−193` is odd, `3 (mod 4)` and `a<193`. The only divisor
of `37248` with those properties is `a=3` (the only odd `3 (mod 4)`
divisors are `3` and `291`, the latter too large). This forces `x=49=7²`.
Every divisor `c|x²=7⁴` is `1 (mod 3)`, so `4c+1≡2 (mod 3)` and no Type-I
certificate exists there. The sorry-free Lean theorem
`no_root_one_typeI_193` certifies precisely this **restricted** failure
(the small factorization is kernel-checked). **This is not a counterexample
to Erdős–Straus**: `4/193=1/50+1/1450+1/27985`. Requiring the
root-of-one exchange for every prime is *strictly stronger* than the
actual conjecture.

For all three requested stress primes, the *general shifted-square criterion*
(1) has honest witnesses (the following are not asserted to extend to all
hard primes):

| `p` | `x` | `a` | `r|x²` | `c=x²/r` | ordered `(x,y,z)` |
|---:|---:|---:|---:|---:|---|
| 193 | 50 | 7 | 10 | 250 | `(50,1380,1331700)` |
| 2521 | 638 | 31 | 3509 | 116 | `(638,51997,23833534)` |
| 6553 | 1640 | 7 | 5 | 537920 | `(1640,1535275,3299895520600)` |

In each row `a|p²+4r`, all denominators satisfy `0<x<y<z`, and the
fraction identity holds by exact integer/rational computation and is
Lean-certified by the `test_*_square_shift` theorems. The file also
checks the previously known ordered identities `(50,1450,27985)` at `193`,
`(638,55462,804199)` at `2521` and `(1640,1612120,32207995)` at `6553`.
Only the last row's displayed `a=7` has `p²≡1 (mod a)`. At `p=193`,
`p²≡2 (mod 7)`, and at `p=2521`, `p²≡7 (mod 31)`; (4) therefore gives
no exchange at those indicated fibers. The `p=6553` second solution with
cofactor `c=5` is the latter of its two displayed triples in (5), with
denominators `(1640,1612120,32207995)`.

**Beatty/Euclidean view of the obstruction.** For each eligible `x`, let
`N=px` and `a=4x−p`. The prospective integer second denominators are
`y=⌊N/a⌋+1, ⌊N/a⌋+2, …`; their positive Euclidean slacks
`r=ay−N` form *one* residue progression modulo `a`. Type I asks for a
positive member of that progression **dividing `x²`**; (1) is its equivalent
shifted-square test. A real approximation, pigeonhole of residue classes, or
a CF convergent does not force this intersection. At `p=193,x=49`, one
has `N=9457≡1 (mod 3)`, so every positive slack is `2 (mod 3)`,
whereas every positive divisor of `49²` is `1 (mod 3)`. The progression is
empty of eligible divisors at this *one fiber* although `193` works at `x=50`.
Scaling known solutions covers composite multiples, not a new prime;
continued-fraction rounding `[0;6k,4]` just returns this failing `x=49`
when `p=193`. The exchange above does not overcome this integrality gap.

**Exact missing step.** The existing certified prime reduction says that
for *every* prime `p=24k+1` one must find `0≤j<6k`, put
`x_j=6k+1+j`, `a_j=4j+3`, and produce **at least one** of

    ∃r>0: r|x_j²  and  a_j|p²+4r                 (Type I, by (1)),
    ∃d: 0<d<x_j, d|x_j²  and  a_j|x_j+d          (Type II).

Alternatively, a disproof needs a **certified prime** and a proof that
*both* conditions fail for *every* eligible `j`. Neither a descent from
smaller inputs (prime inputs do not inherit a solution by scaling), the
continued fraction `[0;6k,4]` (its greedy `x_0` already fails for `193`),
the exchange (4), nor an average/finite residue count forces the needed
pointwise divisor. No proof or counterexample to the original conjecture is
claimed.

**Verification.** `lake env lean Submission/EuclideanExchange.lean` and
`lake build Submission.EuclideanExchange` succeed. An independent
`#print axioms` audit of the construction, progression, obstruction and
sample statements lists only `propext`, `Classical.choice`, `Quot.sound`;
there is no `sorryAx` or `native_decide`. Exact rational arithmetic checks
the displayed numerical identities and several symbolic progression members.
`Spec.lean` was neither imported nor modified.
