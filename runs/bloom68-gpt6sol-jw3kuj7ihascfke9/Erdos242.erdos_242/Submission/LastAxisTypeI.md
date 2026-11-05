# Full Type-I square-divisor symmetry on the last-denominator axis

**Status.** `LastAxisTypeI.lean` proves the auxiliary square-divisor criterion below and its equivalence to the *full* Type-I branch of the existing, strictly ordered prime classification. It also formalizes the last-denominator residue separation and exact ordered examples at `p=193,2521`. The explicit general denominator formula and its bijection are proved here by elementary arithmetic. Neither file imports or edits `Spec.lean`. **None of these facts proves the conjecture.**

Write `Good(p)` for a solution in positive integers `x<y<z` to `4/p=1/x+1/y+1/z`. The earlier classification says that for a prime `p>2`, `Good(p)` is equivalent to some `p/4<x<p/2` satisfying at least one of

* Type I: `c>0`, `c|x²`, `4x-p | 4c+1`;
* Type II: `0<d<x`, `d|x²`, `4x-p | x+d`.

## A square-divisor test for **all** Type-I certificates

For **any** natural number `p`, a Type-I certificate with `p/4<x<p/2` exists if and only if there are positive integers `h,M,c` such that

    4M=hp+1,       0<c<M,       c|M²,       h|M+c.              (A)

No primality assumption is used for this equivalence. The condition is `c|M²`, **not** `c|M`: it covers Type-I certificates not covered by the earlier restricted bilinear test. Lean theorems `lastAxisTypeI_iff_typeI` and `good_iff_lastAxisTypeI_or_typeII` formalize these equivalences (the latter for primes `p>2`).

**Proof, Type I to (A).** Set `a=4x-p>0`; choose `h>0` with `ha=4c+1`, and set `M=hx-c`. Because `a<2x`, we have `4c+1=ha<2hx`, so `2c<hx`, `M>c>0`. Directly,

    4M=4hx-4c=h(a+p)-4c=hp+1,     M+c=hx.

Also `c|x²` implies `c|(hx)²`, hence `c|M²` because `M≡hx (mod c)`.

**Proof, (A) to Type I.** From `4M=hp+1`, every common divisor of `h` and `M` divides `1`, so `gcd(h,M)=1`. Since `c|M²`, also `gcd(h,c)=1`. Define the integer `x=(M+c)/h`. Then

    h(4x-p)=4c+1>0,

so `p<4x`. As `c<M`, `2hx=2M+2c<4M=hp+1`; the integer inequality gives `2hx≤hp`. Equality `2x=p` would make `2hx=h(4x-p)=4c+1`, an even number equal to an odd number. Thus `2x<p`. Finally `c|M²` implies `c|(M+c)²=h²x²`, and `gcd(h,c)=1` implies `c|x²`; the displayed equation gives `4x-p | 4c+1`. This proves the converse with strict bounds.

## Explicit denominators and an integral-point involution

Given (A), let `e=M²/c`. This is a positive integer satisfying `ce=M²`. In fact `c<M<e`: otherwise `ce≤cM<M²`. Moreover,

    c(M+e)=M(M+c),

so `h|M+c` and `gcd(h,c)=1` imply **`h|M+e`**. Consequently the following are integers:

    x=(M+c)/h,        y=(M+e)/h,        z=pM.             (B)

They satisfy `0<x<y<z`. The first inequality follows from `c<e`. For the second, `M≥2`, `e≤M²` (since `c≥1`), and `hp=4M−1`, whence

    h y=M+e≤M+M²<4M²−M=h(pM)=h z.

Multiplying `hx=M+c` and `hy=M+e`, and using `ce=M²`, gives `hxy=M(x+y)`, hence `1/x+1/y=h/M`. Then

    1/x+1/y+1/z = h/M+1/(pM) = (hp+1)/(pM) = 4/p.

For a fixed `M`, the involution `c↔e=M²/c` exchanges the first two denominators; choosing `c<M<e` selects the strict order. The coprimality above shows that integrality of the *second* denominator in (B) is automatic once the first is integral. This is an exact integrality statement, not a local-to-global theorem or a pointwise existence result.

## Last-denominator residue separates the prime branches

Let `p>2` be prime and `(x,y,z)` **any** ordered solution. By the previously proved structural classification, `0<x<p` and `p|z`; write `z=pw` with `w≥1`. Clearing the fraction equation gives

    (4w−1)xy=pw(x+y).                                     (C)

It follows exactly that

    p∤y    ⇔    p | 4w−1.                                  (D)

Indeed, if `p∤y`, then `p∤xy` since `0<x<p`; (C) and primality force `p|4w−1`. Conversely, suppose `p|4w−1`. Then `p∤w`, since otherwise `p` would divide `(4w)−(4w−1)=1`. If `p|y` as well, the left-hand side of (C) is divisible by `p²`. Thus `p|w(x+y)`. As `p|wy`, this implies `p|wx`, contrary to primality and `p∤w,x`. This proves (D), including the converse; `p|4w−1` must **not** be inferred for Type-II solutions.

When `p∤y`, take `M=w` and `h=(4w−1)/p`. Then `1/x+1/y=h/M`, so `c=hx-M`, `e=hy-M` are positive and satisfy `ce=M²` and `c<e`. It follows that `c<M<e`, `h|M+c`, and (A) holds. Thus (B) recovers *every* ordered solution with non-`p`-divisible middle denominator, with its **actual** last denominator `pM`. Conversely (A) gives such a solution by (B) and (D). This is a parametrization of the complete Type-I branch, not just existence of some Type-I solution.

For `p≡1 (mod 4)`, (D) entails `h≡3 (mod 4)` and `h≥3` in the Type-I branch. In particular `z=pw=p(hp+1)/4 ≥ p(3p+1)/4`. No analogous lower bound from this argument applies to Type II: there `p|y`, and (D) says `p∤4w−1`.

## Exact checks, and the missing quantifier

| `p` | `(h,M,c,e=M²/c)` | `(x,y,z)` from (B) |
|---:|---:|---:|
| 5 | `(3,4,2,8)` | `(2,4,20)` |
| 13 | `(3,10,2,50)` | `(4,20,130)` |
| 17 | `(7,30,5,180)` | `(5,30,510)` |
| 73 | `(23,420,40,4410)` | `(20,210,30660)` |
| 97 | `(7,170,68,425)` | `(34,85,16490)` |
| 193 | `(3,145,5,4205)` | `(50,1450,27985)` |
| 2521 | `(15,9454,326,274166)` | `(652,18908,23833534)` |

All entries satisfy the integer relations in (A), the strict inequalities and the fraction identity by exact rational arithmetic. At `p=73,h=23,M=420`, `40|420²` but `40∤420`: a certificate can genuinely require the **square** of `M`. In fact no `c|420`, `0<c<420`, has `23|420+c`: this would require `c≡17 (mod 23)`, whereas the proper positive divisors of `420=2²·3·5·7` are `1,2,3,4,5,6,7,10,12,14,15,20,21,28,30,35,42,60,70,84,105,140,210`; none has that residue. For comparison, existing Type-II solutions at `p=193` and `2521` have respectively `w=z/p=26` and `319`; `4w−1=103` and `1275` are **not** divisible by their respective primes.

**Gap.** To prove Erdős–Straus for the remaining primes `p≡1 (mod 24)`, one still must show, *for each such prime*, either the existence of `h,M,c` in (A) **or** a Type-II divisor at some `p/4<x<p/2`. The involution, the last-denominator congruence, explicit examples and finite verifications supply neither that pointwise disjunction nor a prime for which both alternatives fail. The `Spec.lean` universal assertion remains open.
