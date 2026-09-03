# Exact CRT rounding, favorable lengths, and subinterval rigidity

## Outcome

**Erdős 970 is not resolved here.** No proof of `H(k) = O(k²)`, no counterexample,
and no improvement of the cited uniform `O((k log k)²)` bound is obtained.
In particular, the bound `D(L) ≥ c√L` remains unproved.

The rigorous results of this investigation are:

1. A complete two-modulus criterion for when **ceiling singleton counts force
   a ceiling intersection**, including lengths divisible by either modulus.
   Exactly `p+q−2` nonzero remainders modulo `pq` have this property.
2. A quantitative limitation on favorable-length trimming. For coprime
   `p>1`, `q≥p+2`, and `2≤L<pq`, that forcing requires
   
   ```
   (q−p)(L−1) ≥ p(q−1).
   ```
   The contrapositive gives actual, disjoint, maximal residue columns, not just
   a numerically consistent triple of counts. This implication is Lean-checked.
3. For `L≡1 mod Q`, all intersection rounding bits on the primes of `Q`
   are determined by the singleton bits. Their total inclusion–exclusion
   correction is **zero or minus one**, not a sum of independent unit gains.
4. Exact singleton counts on all length-`p` subintervals already recover
   the actual residue column. This makes precise how much information the
   proposed all-subinterval constraints contain.
5. A covered 17-row integer array passes **every** exact intersection bound
   and **every** two-block CRT-bit compatibility test, including composite
   blocks, but has no common assignment of residue roots. This is a stronger
   finite obstruction than the previous 19-row example. It does not obstruct
   imposing genuinely common roots.

The four new Lean files verify the count criterion, the Euclidean record-set
recursion and general enumeration `p+q−2`, the quantitative gap obstruction,
all-bit remainder-one identity, window rigidity, and the finite counterexample.
The maximum-union formula, strict-`floor+1` enumeration, prefix-count bound,
and consecutive-pair corollary also have written proofs below and independent
regression tests; those further corollaries are not claimed as Lean theorems.
No claim of priority over the mathematical literature is made for these
structural results. They are not a new asymptotic Jacobsthal bound.

`Submission/Spec.lean` was not edited or imported by the new files. Its SHA-256
remains
`c961aa894dc05a671003b74cd770bf0efc120992bcaaa79466c418b03e1688e7`.

## 1. Exact counts and what imposing all CRT roots means

Fix distinct primes `P`, one root `a_p mod p` per prime, and `[0,L)`. For
`S⊆P` put `d_S=∏_{p∈S}p`. Let `r_S∈[0,d_S)` be the unique CRT root of the
chosen singleton roots. Then

\[
 M_S(L)=\left\lfloor\frac L{d_S}\right\rfloor+
 1_{r_S<L\bmod d_S}.                                      \tag{1}
\]

For a shifted interval `[u,u+L)`, replace `r_S` by `(r_S−u) mod d_S`.
The roots for different subsets must arise from the **same** singleton roots.

Equation (1) is `intersection_count_exact`; the pair version is
`pair_count_exact`. Boolean Möbius inversion then gives the actual number of
uncovered positions:

\[
 U(L)=\sum_{S\subseteq P}(-1)^{|S|}M_S(L).                  \tag{2}
\]

Consequently, asking for common singleton roots, the exact count (1) for every
subset, and a covered histogram is **equivalent to the genuine interval
covering problem**. It is not a relaxation with extra independent variables.
This does not make it useless, but deriving a lower bound from it still needs
an aggregate inequality not supplied by the CRT formula alone.

## 2. Complete remainder-one correlation

Let `Q=∏_{p∈P}p` and `L≡1 mod Q`. For every nonempty `S⊆P`, `L mod d_S=1`.
Thus the rounding bit is

\[
 e_S=1_{r_S=0}=\prod_{p\in S}1_{a_p=0}.                    \tag{3}
\]

Since `L mod p=1`, `a_p=0` is exactly the condition that the singleton count
is its ceiling. If `G={p:a_p=0}`, (3) says that `e_S=1` precisely for the
nonempty subsets of `G`. Therefore

\[
 \boxed{\quad
 \sum_{\varnothing\ne S\subseteq P}(-1)^{|S|}e_S
 =-1_{G\ne\varnothing}.
 \quad}                                                   \tag{4}
\]

This is the full correlation, not only the implication for a pair. The Lean
results are `common_remainder_one` and `alternating_rounding_collapse`.
For example, writing `L=mQ+1`, the core leaves exactly
`mφ(Q)+1−1_{G≠∅}` uncovered positions.

### How many primes can be put into such a block by trimming?

For `1<L≤M`, every prime in this block divides `L−1`, so `Q≤M−1`. If the
block has `s` distinct primes, their increasing ordering gives

\[
 (s+1)!\le Q\le M-1.                                      \tag{5}
\]

In particular `s=O(log M/log log M)`. At `M=O(k²)` this is
`O(log k/log log k)`, not a positive proportion of `k`.
For the specific remainder-one pair rule, the favorable pairs at one length
are exactly the pairs of primes dividing `L−1`: a single clique, not an
arbitrary large graph of independently favorable products. Changing the
starting point changes the singleton bits but not these length remainders.

This only limits the simultaneous remainder-one strategy. It does **not**
exclude using different remainders or different lengths for different primes.
The next sections analyze all remainders for the ceiling–ceiling implication.

## 3. All two-modulus rounding correlations of the specified type

Let `p,q>1` be coprime, `N=pq`, and `C(p,q;a,b)` be the CRT root in `[0,N)`.
A grid point `(a,b)`, `0≤a<p`, `0≤b<q`, is a **prefix record** when

\[
 C(p,q;a,b)=\max_{0\le x\le a,\ 0\le y\le b} C(p,q;x,y).
                                                               \tag{6}
\]

Let `R(p,q)` be the set of record points. Define

\[
 F(p,q)=\{t:1\le t<N,\ ((t-1)\bmod p,(t-1)\bmod q)\in R(p,q)\}.
                                                               \tag{7}
\]

### The exact criterion

For `0<t<N`, a residue `a` modulo `p` has the ceiling count in `[0,t)` iff

\[
 a\le (t-1)\bmod p.                                       \tag{8}
\]

This formulation matters when `p|t`: the right side is then `p−1`, so every
residue is maximal. Using `a<t mod p` in this case would incorrectly exclude
all residues. `residueCount_max_iff` verifies (8).

The possible joint CRT roots for two maximal singleton columns are exactly
the grid rectangle in (6), with corner `((t−1) mod p,(t−1) mod q)`. The root
at that corner is `t−1`. Thus **every** such root is below `t` iff that corner
is a prefix record. Equivalently,

\[
 t\in F(p,q)
 \iff \text{two ceiling singleton counts force the joint ceiling}. \tag{9}
\]

The Lean theorem `forcing_iff_maximal_counts` proves this equivalence directly
in terms of actual occurrence counts for `0<L<pq`.

### An exact maximum-union bound

For every `L≥0`, put `t=L mod N`. Maximizing over the two residue choices gives

\[
 \boxed{\quad
 \max_{a,b}|([0,L)\cap(a\bmod p))\cup([0,L)\cap(b\bmod q))|
 =\left\lceil\frac Lp\right\rceil+
   \left\lceil\frac Lq\right\rceil-
   \left\lfloor\frac L{pq}\right\rfloor-1_{t\in F(p,q)}.
 \quad}                                                       \tag{10}
\]

**Proof.** Remove full `pq` periods. When `t=0`, all counts are fixed and the
formula is immediate. When `t>0`, the independent upper bound is attained
exactly if both singleton counts are ceilings and the joint count is its
floor. Criterion (9) decides whether this is possible. If it is impossible,
the upper bound drops by at least one: either a singleton loses one or the
intersection gains one. It drops by at most one, because choosing both
singleton roots zero gives both ceilings and the joint ceiling. This proves
(10), including the boundary cases in (8).

Examples:

```
F(2,3) = {1,4,5}.
F(3,5) = {1,7,11,12,13,14}.
```

At `L=19`, `p=2`, `q=3`, (10) gives `10+7−3−1=13`, rather than the independent
rounding upper bound `14`. At `L=7`, `p=3`, `q=5`, it gives `3+2−1=4`, although
`7` is not congruent to `1` or `−1` modulo `15`.

## 4. Euclidean classification and exact number of favorable remainders

The record sets obey a simple Euclidean recursion, formalized as
`RecordCount.records_reduce`. For `p<q`,

\[
 R(p,q)=R(p,q-p)\ \dot\cup\
 \{(i,q-p+i):0\le i<p\}.                                  \tag{11}
\]

There is a transposed recursion for `q<p`, and `R(1,q)` is the entire
one-row grid.

### Proof of the recursion

In the subrectangle `0≤a<p`, `0≤b<q−p`, write a root as

\[
 C(p,q;a,b)=b+qj,\qquad 0\le j<p.
\]

The root for moduli `p,q−p` is `b+(q−p)j`: it has the same residues, and is
in the required range. Comparisons of two roots in either grid are exactly
lexicographic comparisons of `(j,b)`, since `0≤b<q−p`. Thus **all root orders
on that subrectangle are preserved**, so its record points are precisely
`R(p,q−p)`.

In the remaining strip `q−p≤b<q`, the points
`D_i=(i,q−p+i)` have roots `N−p+i`. These are the largest `p` roots in the
whole grid, and each `D_i` is a prefix record. Every other point in the strip
has root below `N−p`. Its prefix rectangle contains
`D_min(a,b−(q−p))`, whose root is at least `N−p`. Hence that other point is not
a record. This proves (11), with disjoint union.

Subtractive Euclidean induction now gives

\[
 |R(p,q)|=p+q-1.
\]

The record with root `N−1` corresponds to `t=N`, excluded from (7). Therefore

\[
 \boxed{|F(p,q)|=p+q-2.}                                  \tag{12}
\]

The general count is kernel-checked as `RecordCount.card_favorable`; its
record-count predecessor is `RecordCount.card_records`.

So a uniformly sampled full-period length remainder is favorable with
probability exactly `1/p+1/q−2/(pq)`. Sampling only an `O(k²)` length window
is not sampling a full period when `p,q` are of size `k log k`.

If one insists on the stricter convention that both singleton counts are
`floor+1` (so both singleton remainders must be nonzero), then, for `p<q`,

\[
 |\{t\in F(p,q):p\nmid t,\ q\nmid t\}|
 =p+q-2-\lfloor q/p\rfloor.                               \tag{13}
\]

Indeed this deletes record points on the last row or last column. The last
column contains only `(p−1,q−1)`. The last-row record points have
`b≡q−1 mod p`, of which there are `floor(q/p)+1` since `p∤q`. Their union has
that same cardinality; subtract it from `p+q−1`.

### A prefix, rather than full-period, counting bound

For `1≤T<N`,

\[
 |F(p,q)\cap[1,T]|
 \le \lceil T/p\rceil+\lceil T/q\rceil-1.                  \tag{14}
\]

Here is a proof that does not assume uniform sampling. There is a bijection
from the grid boundary `{a=0 or b=0}` to `R(p,q)` which never decreases the
CRT root. Construct it recursively using (11). The old boundary-to-record
bijection remains order-increasing because of the order preservation on the
smaller rectangle. Match each new boundary point `(0,q−p+i)` to `D_i`.
For `i=0` their roots agree; for `i>0` the boundary root is below `N−p`, while
the record root is above it. Transpose when necessary; the one-dimensional
base case is the identity. This constructs the claimed bijection.

The inverse map sends records with root `<T` into boundary points with root
`<T`. Boundary roots are exactly the multiples of `p` or `q`; in `[0,T)`
there are `ceil(T/p)+ceil(T/q)−1` of these. This proves (14).

Equations (11)–(12) have general Lean proofs, and (13)–(14) have the written
proofs above; none is inferred from finite data. The verifier independently
compares the recursion with direct CRT grids for 1,380 coprime pairs, including
composite moduli.

## 5. A quantitative obstruction to favorable-length trimming

Let

```
x = C(p,q;1,0),    y = C(p,q;0,1).
```

Every nonzero prefix record has root at least `min(x,y)`: any non-origin
prefix rectangle contains `(1,0)` or `(0,1)`. Conversely the point realizing
`min(x,y)` is itself a record, since its rectangle contains only it and the
origin. Consequently the first favorable length after `1` is exactly

\[
 1+\min(x,y).                                             \tag{15}
\]

Assume `q≥p+2`, and put `d=q−p`. Writing `x=qv`, its congruence modulo `p`
gives `dv≡1 mod p`. Since `d≥2` and `v≥1`, `dv` cannot be `1`, so
`dv≥p+1`. Hence `dx≥q(p+1)`. Similarly, writing `y=pu`, its congruence
modulo `q` gives `du≡−1 mod q`, and `du≥q−1`. Hence `dy≥p(q−1)`.
Together with (15), this proves

\[
 \boxed{\quad
 2\le L<pq,\ L\in F(p,q)
 \Longrightarrow (q-p)(L-1)\ge p(q-1).
 \quad}                                                    \tag{16}
\]

The condition `q≥p+2` is essential; this argument does not apply to consecutive
moduli such as `5,6`. For two odd primes it is automatic.

The Lean theorems `record_gap_bound` and `forcing_gap_bound` prove (16).
Moreover `disjoint_maximal_columns_of_small_gap` proves its concrete
contrapositive:

\[
 2\le L<pq,\quad (q-p)(L-1)<p(q-1)
 \Longrightarrow
 \begin{cases}
 \text{there exist ceiling-count residue columns modulo }p,q,\\
 \text{and their actual intersection in }[0,L)\text{ is empty}.
 \end{cases}                                               \tag{17}
\]

For example, for `101,103` the neighboring roots are `5253,5151`, so the
first nontrivial favorable length is `5152`. At length `1000` both columns
can have their maximal count `10` and be disjoint. The latter statement is
also checked as an instance of the general Lean theorem.

### Uniformly over a whole trimming window

Take an increasing list of odd primes in `[A,B]`, with `A>1`, and pair
consecutive primes without overlap. Let `2≤M<A²`. Among these pairs, the
number that can be favorable for **any** length `2≤L≤M` is at most

\[
 \boxed{\frac{(B-A)(M-1)}{A^2}.}                           \tag{18}
\]

Indeed each such pair has
`q−p ≥ p(q−1)/(M−1) ≥ A²/(M−1)` by (16). The sum of the disjoint consecutive
pair gaps is at most `B−A`.

For illustration, pair the upper half of the first `k` primes consecutively.
Using their standard size `p_j≍k log k` in this range, (18) says that at most
`O_C(k/log k)` of the `Θ(k)` pairs can have a nontrivial favorable length
anywhere below `Ck²`. Thus averaging or adaptively trimming within that range
cannot supply this ceiling–ceiling forcing for most of those close pairs.
Each correction in (10) is only one, so the improvement from these particular
paired capacities is at most `O_C(k/log k)`.

**Scope of this conclusion.** This is a bound on a specified rounding
mechanism, not on all possible CRT arguments. It does not exclude using other
pairings, overlapping constraints, large blocks, phase information, smaller
primes, or the full covering hypothesis. In particular it is not an
impossibility theorem for proving `H(k)=O(k²)` by exact arithmetic.

## 6. Even all two-block bit tests do not give common roots

Consider the following covered histogram on `[17]`, with
`P={2,3,5,7,11}`:

| Exact support | Multiplicity |
|---|---:|
| `{2}` | 5 |
| `{3}` | 3 |
| `{2,3}` | 1 |
| `{5}` | 2 |
| `{2,5}` | 1 |
| `{2,3,5}` | 1 |
| `{7}` | 2 |
| `{2,3,7}` | 1 |
| `{11}` | 1 |

All multiplicities are nonnegative integers, total `17`, and the empty
support has multiplicity zero. Every one of the 32 intersection counts is
its exact floor or ceiling. In mask order on `(2,3,5,7,11)`, the counts are

```
[17,9,6,3,4,2,1,1,3,1,1,1,0,0,0,0,
  1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0].
```

This array passes the following substantially stronger test. For every pair
of disjoint nonempty blocks `A,B⊆P`, there exists a root `r<d_A d_B` such that

\[
\begin{aligned}
 M_A&=\lfloor17/d_A\rfloor+1_{r\bmod d_A<17\bmod d_A},\\
 M_B&=\lfloor17/d_B\rfloor+1_{r\bmod d_B<17\bmod d_B},\\
 M_{A\cup B}&=\lfloor17/(d_A d_B)\rfloor+1_{r<17\bmod(d_A d_B)}.
\end{aligned}                                               \tag{19}
\]

This checks **all three bits and all their possible incompatibilities**, not
only the ceiling–ceiling implication. It includes every composite block.
There are 90 unordered, or 180 ordered, block pairs; each has a witness
`r<46`, as well as `r<d_A d_B`. The complete finite statement is Lean-checked
as `all_block_pairs_compatible17`, and the independent verifier includes a
fixed list of all 90 witnesses.

### Why it still has no common residue assignment

Only five of its counts are needed:

```
M2=9, M3=6, M7=3, M27=1, M237=1.
```

- `M2=9` forces the root modulo 2 to be `0`.
- `M7=3` restricts the root modulo 7 to `0,1,2`.
- With the even column fixed, the corresponding roots modulo 14 are `0,8,2`.
  At length 17, the joint count is `1` only for root `8`. Thus the modulo-7
  root is `1`, and the unique common 2-and-7 position is `8`.
- `M3=6` restricts its root to `0` or `1`. Neither contains `8`, whose residue
  modulo 3 is `2`. Thus `M237` must be zero, contrary to its displayed value 1.

The finite normalized impossibility and its unbounded-residue normalization
are separately Lean-checked as `no_normalized_realization17` and
`no_residue_realization17`.

This example refutes the replacement of common CRT roots by compatibility
of each pair of block bits. The witnesses in (19) may, and do, disagree from
one block pair to another. **It is not a counterexample when one common root
is imposed for every singleton and all subsets inherit it.** Its ratio
`17/5²` also supplies no asymptotic obstruction to a quadratic bound.

## 7. Subinterval constraints already recover position arithmetic

Let `b(0),...,b(L−1)` be a Boolean column and `1≤p≤L`. Then

\[
 \left[\text{every contained length-}p\text{ window has exactly one hit}\right]
 \iff
 \left[\exists r<p:\ b(i)=1\iff i\equiv r\pmod p\ (0\le i<L)\right].
                                                               \tag{20}
\]

**Proof.** Subtract the counts on adjacent windows starting at `a` and `a+1`.
The entering and leaving bits must agree: `b(a+p)=b(a)`. The first window
contains exactly one hit. Propagate it using this period relation. Conversely,
one complete residue period has exactly one hit, whatever its start.

`one_windows_iff_residue` proves both directions in Lean. It does not assume
primality, intersection counts, or covering.

For `p>L`, the global upper bound permits at most one hit. Any singleton hit
is one residue class on the interval; if there is no hit, choose a residue
in `[L,p)`. Thus exact singleton floor/ceiling bounds on **all subintervals**
already characterize full residue columns, even before adding intersection
constraints. Full covering of such an array is the original covering problem.

This explains why cumulative constraints cannot be treated as independent
floor errors. It does not provide a lower bound for the cost of a cover.

Nor can one assert that subinterval averaging automatically produces overlap
among the large primes. For any distinct primes with all pair products `>M`,
choose roots `a_p=p−1`. On `[0,M)`, membership means `p|(i+1)`, so no position
has two labels: their product would divide a positive integer at most `M`.
This remains true on **every** contained subinterval. The example can use
primes between `√M` and `M`, not merely singleton primes `p≥M`. It is
explicitly not a full cover (position zero is uncovered); it only rules out
an unconditional overlap claim based on exact subinterval arithmetic alone.

## 8. The covering cost and the legitimate finite prime cutoff

Define

\[
 D(L)=\min_{P,\,a}\bigl(|P|+U(P,a;L)\bigr),\qquad L\ge1,
                                                               \tag{21}
\]

with distinct primes and one residue per prime. This can equivalently be
minimized over **primes `p<L` only**. Each class with `p≥L` hits at most one
position; removing all such classes increases the survivor count by at most
the number of removed primes, so does not increase the cost. The remaining
optimization is finite, including finitely many residue choices.

Conversely, fill every surviving position with its own fresh prime `≥L`,
chosen distinct from the others. Each costs one and covers just that position
in the interval. It follows that

\[
 D(L)=\text{minimum number of distinct primes in a genuine cover of }[0,L).
                                                               \tag{22}
\]

CRT turns an arbitrary residue cover into a translate of divisibility by
those same primes. Accordingly, for the uniform Jacobsthal function,

\[
 D(L)\le k\quad\Longleftrightarrow\quad H(k)>L.             \tag{23}
\]

The endpoint convention is important: `H(k)` is one more than the longest
covered length. Thus `H(k)≤Ck²` implies `D(L)>√(L/C)`, while
`D(L)≥c√L` implies

\[
 H(k)\le\lfloor k^2/c^2\rfloor+1.
\]

So the proposed cost lower bound is essentially **equivalent to**, not weaker
than, the target conjecture. The cited `O((k log k)²)` result only yields
`D(L)≫√L/log L`. Nothing here improves that uniform lower bound.

### Finite sanity check: `D(19)=6`

This is a small known-scale value, not a new asymptotic result. An elementary
all-prime lower-bound argument avoids any primorial reduction:

1. Without prime 2, five distinct primes cover at most
   `ceil(19/3)+ceil(19/5)+ceil(19/7)+ceil(19/11)+ceil(19/13)=18` positions.
2. With 2 but without 3, at least 9 positions of the other parity remain.
   In that parity progression, four distinct primes at least `5,7,11,13`
   cover at most `2+2+1+1=6` positions (use its length at most 10).
3. With both 2 and 3, each block of six leaves two positions, so at least
   six remain in a length-19 interval. For the three remaining primes, the
   parity restriction bounds their contributions by at most `2,2,1`: their
   unrestricted occurrence counts are at most `4,3,2`, respectively, and
   those occurrences alternate parity. Thus they cover at most five of the
   remaining positions.

These cases exclude all covers with at most five primes, including arbitrarily
large primes. Six primes do cover `[0,19)`; one explicit residue list is

```
prime:    2  3  5  7  11  13
residue:  0  1  0  3   0   9
```

The verifier checks every position. The sorted-prime capacity comparisons in
the lower bound do not assert that replacing primes preserves a cover.

## 9. Verification and files

New files:

- `Submission/CRTWindowArithmetic.lean`: exact pair count, maximal singleton
  criterion, record/forcing equivalence, nearby-moduli gap bound, and actual
  disjoint maximal columns under its strict reverse inequality.
- `Submission/CRTWindowRigidity.lean`: exact all-subset counts, full
  remainder-one bit formula and inclusion–exclusion collapse, and finite
  one-period-window rigidity in both directions.
- `Submission/CRTWindowRecords.lean`: the order-preserving Euclidean reduction
  of the CRT grid, exact disjoint record-set recursion, record count `p+q−1`,
  and favorable-remainder count `p+q−2`.
- `Submission/CRTWindowExamples.lean`: the covered 17-row histogram, all
  intersection constraints, all 180 ordered block-pair compatibility checks,
  no common roots, and the `101,103,1000` instance.
- `Submission/verify_crt_windows.py`: independent exact-integer tests and fixed
  finite certificates, with no numerical optimizer or floating point.
- `Submission/CRTWindowLeanCheck.log` and
  `Submission/CRTWindowFiniteCheck.log`: successful verification output.

From `/workspace/leanproject`:

```sh
lake env lean -o .lake/build/lib/lean/Submission/CRTWindowArithmetic.olean \
  Submission/CRTWindowArithmetic.lean
lake env lean -o .lake/build/lib/lean/Submission/CRTWindowRigidity.olean \
  Submission/CRTWindowRigidity.lean
lake env lean -o .lake/build/lib/lean/Submission/CRTWindowRecords.olean \
  Submission/CRTWindowRecords.lean
lake env lean -o .lake/build/lib/lean/Submission/CRTWindowExamples.olean \
  Submission/CRTWindowExamples.lean
python3 Submission/verify_crt_windows.py
```

All theorem roots printed in the log use only `propext`, `Classical.choice`,
and `Quot.sound`; there is no `sorryAx` or imported conjectural assumption.
Finite Lean checks use `decide`, not `native_decide`.

The independent verifier checked:

- Euclidean record classification, record counts, both favorable-count
  formulas, the order-increasing boundary bijection, prefix bounds, and gap
  bounds for 1,380 coprime pairs;
- formula (10) against every residue phase at 7,350 lengths, including
  integral-count boundary cases;
- the fixed 17-row histogram and all block-pair witnesses;
- its five-count incompatibility over all 42 normalized choices;
- the six-prime 19-position cover and an explicitly noncovering disjoint-large-
  prime example;
- all-bit remainder-one cancellation over every phase of `{2,3,5}` at `L=61`;
- the unchanged hash of `Spec.lean`.

The two prior independent verification scripts also still pass.

## 10. Remaining mathematical gap

The positive finding is that exact CRT rounding does give strong, explicit
correlations missed by independent floor/ceiling counts, and even by all
pair-of-block bit tests. The negative finding is quantitative: favorable
maximal-singleton forcing is sparse and, for close large primes, may be
unavailable throughout the proposed trimming window.

Neither finding controls the aggregate Möbius correction under **one common
root assignment and full covering**. A proof still needs a genuinely global
inequality using those hypotheses to show that fewer than `c√L` prime classes
cannot cover all positions. No such inequality has been derived here. The
full multi-scale formulation remains a possible approach, but its mere
exactness is not an upper-bound proof.

Baseline references are the same as in the earlier reports: Costello–Watts,
*A short note on Jacobsthal's function*, arXiv:1306.1064, introduction, for
Iwaniec's uniform `O((k log k)²)` bound; and Banks–Ford–Tao, *Large prime gaps
and probabilistic models*, arXiv:1908.08613, interval-sieve/Jacobsthal section,
for the interval-sieve context. No primorial-maximization assumption is used.
