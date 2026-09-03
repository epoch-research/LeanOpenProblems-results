# WR research gate: unresolved

## Outcome

**This investigation did not prove WR, disprove the existence of a universal
constant in WR, or settle CW.** In particular, it does not prove the sharp
Erdős distinct-distances bound. The finite tests below are not evidence of a
uniform bound over all planar point sets. No Lean theorem or conditional
wrapper was added, and `Submission/Spec.lean` was not modified.

What was verified:

* An exact absorption estimate for the normalized mass carried by axes with
  a bounded number of actual centers. This removes the one-center issue as a
  separate obstacle, but does not solve the two-center capped estimate.
* Exact computations retaining the global positive distance palette, the full
  pinned fibers, actual line occupancies, ordered reflection counts, and the
  cap `min(w,m(m-1))`.
* The particular choice `C=1` is false. This is **not** a counterexample to WR
  with an unspecified universal constant.

## 1. One-center mass can be absorbed without changing the weights

Let `T` be the set of ordered triples `(p,a,b)` of distinct points of `P`
with `|p-a|²=|p-b|²`. If `s=|p-a|²`, give this triple weight

    1/(D k_{p,s}).

This is exactly the question's weight `2/(D k_{p,s})` on triples with an
unordered endpoint pair. Thus the total mass is exactly `B`.

For a real `M>=1`, let `L_M` be the mass on triples whose perpendicular
bisector has at most `M` points of `P`, and put `H_M=B-L_M`. Then

    L_M² <= M n²(n-1)/D <= M n(B+n),                         (1)
    B <= 2 H_M + (M+1)n.                                    (2)

### Proof

Each ordered endpoint pair has exactly one bisector, so

    sum_l w_l = n(n-1).

If `T_M` is the set of triples defining `L_M`, it follows that

    |T_M| = sum_{l:m_l<=M} m_l w_l <= M n(n-1).

For a full pinned fiber of size `k`, all its ordered distinct endpoint
pairs contribute `k(k-1)/k² <= 1` to the sum of inverse squared fiber sizes.
Restriction to `T_M` can only decrease that sum. Therefore

    sum_{(p,a,b) in T_M} 1/k_{p,|p-a|²}² <= sum_p d_p <= nD.

Cauchy–Schwarz now gives the first inequality in (1). The second follows
from `n(n-1)/D = B + (sum_p d_p)/D <= B+n`.

Finally,

    [B+(M+1)n]² - 4Mn(B+n) = [B-(M-1)n]² >= 0.

All quantities being nonnegative, (1) implies
`L_M <= [B+(M+1)n]/2`. Substitute `L_M=B-H_M` to obtain (2). QED.

In particular, with `H=H_1` the exact normalized mass on axes with at least
two actual centers,

    B <= 2H+2n,        B² <= 8H²+8n².                        (3)

Consequently the remaining problem is still

    H² <= C (n² + sum_{l:m_l>=2} m_l min(w_l,m_l(m_l-1))).   (4)

**No proof of (4) was found.** The preceding argument does not estimate the
interaction between masses on different axes, nor does it justify the cap.
It must not be presented as the requested closing inequality.

The `n²` term cannot be removed even after restricting to two-center axes:
for a regular even `n`-gon, `H=B=n-2` and `R=2n`, so `H²/R` is unbounded.
This does not contradict either (4) or WR.

## 2. Exact finite tests

The reproducible command is

    python3 Submission/verify_wr_investigation.py --families

Output is in `Submission/wr_investigation_verification.txt`.

Two independent counting methods are compared:

1. Count `w_l` from endpoint pairs. Separately count unordered collinear
   point pairs on each line, and recover `m_l` from `binom(m_l,2)`.
2. Enumerate the full pinned fibers, group their isosceles witnesses by
   bisector, and count the actual centers directly. At each center of an
   axis the ordered witness count is the same `w_l`.

For small sets there is a further independent check using the exact rational
reflection map. The normalized weight identity and (1)–(2) are checked with
rational arithmetic. All 1,506 instances consisting of subsets of a 3-by-3
coordinate box with at least two points, in three positive-definite metrics,
passed these checks. Both counting methods also agreed on ten lattice disks,
including the 1,459-point triangular disk below.

Additional tests cover square grids up to 1,024 points, triangular
parallelograms, rational rectangular metrics, random thinnings, three-parity-
class subsets, annuli, and periodic parabola/circle residue patterns and circle
complements. These produced no unbounded counterexample family. Finite tests
cannot prove that such a family does not exist.

Representative exact statistics (`B²/(n²+R)` is rounded):

| Set | n | D | sum d_p | R | B²/(n²+R) |
|---|---:|---:|---:|---:|---:|
| 16-by-16 square grid | 256 | 119 | 21,968 | 189,040 | 0.520361 |
| 32-by-32 square grid | 1,024 | 430 | 307,268 | 3,868,880 | 0.602725 |
| Square-lattice disk, radius 20 | 1,257 | 501 | 440,309 | 5,923,920 | 0.688156 |
| Triangular-lattice disk, radius 4 | 61 | 23 | 1,106 | 8,568 | 1.003390 |
| Triangular-lattice disk, radius 20 | 1,459 | 422 | 441,002 | 9,044,940 | 1.428926 |

### An explicit obstruction to C=1, not to universal WR

Define

    P_L = {(a+b/2, sqrt(3)b/2) : a,b integers,
                                a²+ab+b² <= L²}.

For `L=4`, the positive squared-distance palette is

    {1,3,4,7,9,12,13,16,19,21,25,27,28,31,36,37,39,43,48,49,52,57,64}.

The pinned support histogram is

| d_p | number of centers |
|---:|---:|
| 8 | 1 |
| 11 | 6 |
| 14 | 6 |
| 15 | 6 |
| 18 | 12 |
| 19 | 6 |
| 21 | 6 |
| 22 | 12 |
| 23 | 6 |

The occupied bisectors contributing to `R` give:

| m_l | number of axes | sum w_l | contribution to R |
|---:|---:|---:|---:|
| 2 | 222 | 636 | 888 |
| 3 | 78 | 300 | 900 |
| 4 | 18 | 540 | 864 |
| 5 | 15 | 516 | 1,500 |
| 6 | 6 | 60 | 360 |
| 7 | 6 | 132 | 924 |
| 8 | 6 | 216 | 1,728 |
| 9 | 3 | 156 | 1,404 |

Thus

    B = 2554/23,
    B²/(n²+R) = 6522916/6500881 > 1.

The independently cross-checked `L=20` example requires any valid universal
constant to satisfy

    C >= 710834472100/497460780541 = 1.4289256558616565...

Neither calculation gives divergence of this ratio and neither refutes the
WR requested in the question.

## 3. Literature and completion fallback

The checked source of Oliver Roche-Newton, *On sets with few distinct
distances*, arXiv:1608.02775, proves the existence of a reflection overlap of
size `Omega(K³)` through weighted Szemerédi–Trotter and a raw isosceles count.
It does not supply (4) or a lower bound for the required capped occupied-axis
sum.

Ben Lund, Adam Sheffer and Frank de Zeeuw, *Bisector energy and few distinct
distances*, arXiv:1411.6868, studies `sum_l w_l²`, with line/circle concentration
parameters. Its stated bisector-energy proof uses Guth–Katz. That statistic
and those upper bounds do not supply the missing normalized lower bound for
`R`.

The finite-completion reduction in the question is valid: fixing two distinct
points `u,v` of the original set confines every added point to intersections
of one palette-radius circle about each anchor. There are at most `2D²`
such candidates, plus the two anchors. One must select a mutually compatible
subset of these candidates; taking all candidates is not justified. A greedy
maximal compatible extension terminates and keeps exactly the original palette.

However, maximality alone was not shown to imply (4) or WR. No palette-maximal
counterexample was found, and no theorem producing an admissible missing point
from failure of WR was obtained. **CW therefore remains unresolved as well.**

## File integrity

No Lean files were modified. The checked SHA-256 of `Submission/Spec.lean` is

    c2fbaabe5ad8088f856ca97625747c7a01754f3c149dd6a493454e776de290db
