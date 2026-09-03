# Erdős 371: exact cycle/cofactor conservation, and a cyclewise contraction obstruction

## Outcome and scope

**No proof of natural density 1/2 is claimed.** This investigation gives an exact cycle-level conservation law and a precise obstruction to converting it into an automatic contraction. It does not use a pointwise Euclidean switch, an operator moment, or an unproved progression estimate. No Lean file was opened, imported, or edited.

The principal conclusions are:

1. For every integer `N>=2`, the actual edges `N<=n<2N` already form a closed walk in the complete largest-prime-factor graph. They decompose into genuine directed simple cycles, with **no artificial edge and no discarded remainder**.
2. Factor all the integer cofactors on these cycles. Every resulting prime label is at most `sqrt(2N)`, and the **total valuation imbalance is exactly one factor of 2**. Thus almost-perfect lower-scale mass conservation is not a conjectural missing input: it is already exact.
3. A tiny positive product defect has the opposite of the hoped-for implication for absolute factor mass. A cycle of length `r` in this interval has reduced numerator/denominator logarithmic mass at least `2 log(N/(2r))`. Its factor imbalance can be large even though its product ratio is extremely close to 1.
4. There are, unconditionally, arbitrarily large genuine directed prime cycles in an arbitrarily narrow fixed-ratio interval, of any prescribed length `r>=3`, with ordering current `2-r`. Their cofactor-product ratio is `1+O(1/N)`, but, **even after all common prime factors are canceled**, their logarithmic factor-defect norm divided by their original prime-incidence logarithmic mass tends to **1**, not to a constant below 1. These are not the bounded-multiplicity vertices near `X` from the earlier skew-norm obstruction.
5. The total factor-defect vector does not retain ordering current. This can be seen both on actual dyadic prime walks and on an actual closed cofactor-integer cycle with zero defect and nonzero ordering current. A lower prime graph must retain additional edge-pairing information, whose circulation is not determined by mass conservation.

These results obstruct a **uniform cyclewise logarithmic-mass descent**, and any descent that retains only net prime-factor inventory. They do **not** rule out a more selective, sign-sensitive cancellation between different cycles. The infinite examples are sparse and have prime labels of size `N^(1/2+o(1))`; they are not counterexamples to natural density, nor to a conjecture restricted to a fixed high-prime exponent sector.

## 1. An exact dyadic cycle decomposition

Put

```
P(1)=1,
s(n)=sgn(P(n+1)-P(n)),
S(X)=sum_{1<=n<=X} s(n),
W(N)=sum_{N<=n<2N} s(n).
```

For every `N>=2`,

```
P(2N)=P(N).                                               (1)
```

Consequently the word

```
P(N), P(N+1), ..., P(2N)
```

is a closed directed walk. Repeated-vertex loop erasure partitions its edges into directed simple cycles. Every edge retains its original integer index `n`; no synthetic return edge is introduced. In particular, if the cycles are `Gamma_j`, then

```
W(N)=sum_j W(Gamma_j),    sum_j length(Gamma_j)=N.          (2)
```

All prime classes are included. This argument would not be valid after restricting to an induced graph on high primes.

The target `S(X)=o(X)` is equivalent to `W(N)=o(N)` for **all** integers `N` tending to infinity. Necessity is immediate. For sufficiency, peel off `[M,2M)` with `M=floor((X+1)/2)` from a prefix; there is at most one endpoint error. Iterating gives a geometric sum of the dyadic bounds and `O(log X)` endpoint errors. Thus (1) has removed the graph boundary without changing the natural-density problem.

### Cofactor factorization on one cycle

Let a directed cycle have prime vertices `p_1,...,p_r`, and edge indices `n_i`, so

```
n_i=a_i p_i,    n_i+1=b_i p_(i+1),    p_(r+1)=p_1.
A_Gamma=prod_i a_i,    B_Gamma=prod_i b_i.
```

For a prime `ell`, write `v_ell(m)` for its valuation, and define

```
D_Gamma(ell)=sum_i (v_ell(b_i)-v_ell(a_i)).
delta_Gamma=sum_ell D_Gamma(ell) log ell.
```

These retain the entire factorization of both cofactor products, not merely their real-valued logarithms. Exact cancellation of the original cycle vertices gives

```
B_Gamma/A_Gamma = prod_i (n_i+1)/n_i > 1,
delta_Gamma = sum_i log(1+1/n_i) > 0.                     (3)
```

If `ell` divides the cofactor `m/P(m)`, then `ell P(m)` divides `m` and `ell<=P(m)`. This includes the case `ell=P(m)`, when its square divides `m`. Therefore

```
ell^2<=m.                                                (4)
```

Every prime appearing in these cofactor defects is thus at most `sqrt(2N)`.

### All cycles together: exactly one factor of 2

Let `F(m)=(v_ell(m))_ell`, let `e_p` be the unit vector at prime `p`, and put

```
kappa(m)=F(m)-e_(P(m))=F(m/P(m))   (m>=2).
```

Summing over all actual edges of the dyadic interval telescopes:

```
sum_j D_Gamma_j
 = kappa(2N)-kappa(N)
 = e_2.                                                   (5)
```

In particular,

```
sum_j delta_Gamma_j=log 2.                                (6)
```

Equations (4)-(6) are a genuine lower-scale factor-mass conservation law. They require no prime independence and no estimate for arithmetic progressions. The unresolved question is whether a **signed ordering current**, not just this inventory, can be transferred along with it.

## 2. Small product error means a potentially large absolute factor defect

For a signed prime-valuation vector use the logarithmic norm

```
||D||_log = sum_ell |D(ell)| log ell.
```

Writing `g=gcd(A_Gamma,B_Gamma)`, `A'=A_Gamma/g`, and `B'=B_Gamma/g`, one has exactly

```
||D_Gamma||_log = log A' + log B'.                         (7)
```

Because `B'>A'` are integers,

```
B'-A'>=1,
A'>=1/(exp(delta_Gamma)-1).
```

Hence the sharper bound is

```
||D_Gamma||_log
 >= delta_Gamma-2 log(exp(delta_Gamma)-1)
 = -2 log(2 sinh(delta_Gamma/2)).                          (8)
```

For a cycle of length `r` whose edges all satisfy `n_i>=N`,

```
delta_Gamma<=r/N.
```

For `r<=N`, use `exp(r/N)-1<=2r/N` to get the convenient consequence

```
||D_Gamma||_log >= 2 log(N/(2r)).                          (9)
```

A negative right side is simply a vacuous lower bound. For bounded-length cycles at large positions it is asymptotic to `2 log N`.

Thus replacing the integer products by the scalar `log(B/A)` is badly conditioned. Smallness of that scalar is cancellation **between different prime logarithms**, not smallness of the vector of prime-factor supplies and demands.

If there are `K` cycles in the dyadic decomposition, (6), (8), and convexity also give

```
sum_j ||D_Gamma_j||_log
 >= -2K log(2 sinh((log 2)/(2K)))
 = 2K log(K/log 2)+O(1/K).                                (10)
```

The combined vector nevertheless has norm exactly `log 2` by (5). Substantial cancellation of factor inventories between cycles is intrinsic to this setup. No assertion that `K` has a particular asymptotic size is being made; (10) alone is not a linear lower bound in `N`.

### Full prefixes also have a controlled factor boundary

For completeness, loop erasure of `P(1),...,P(X+1)` leaves a simple path of at most `pi(X+1)` edges. This is an `O(X/log X)=o(X)` loss for the bounded ordering observable.

More is true for its cofactor logarithmic mass. A prime vertex `p` is used at most once by the remaining simple path, and each of its at most two incidences has cofactor at most `(X+1)/p`. Therefore

```
sum_{n in residual path} [log(n/P(n))+log((n+1)/P(n+1))]
 <= 2 sum_{p<=X+1} log((X+1)/p)
 = O(X/log X).                                           (11)
```

The last bound follows from the Chebyshev bound `pi(t)<<t/log t` and partial summation. The vertex `1`, if present, has cofactor 1 and adds zero. After factoring, the total defect of the retained cycles has norm `O(X/log X)` as well: it is the endpoint cofactor vector minus the residual-path defect. This is a verified `o(X)` **inventory-boundary** remainder, not an `o(X)` estimate for `S(X)`.

## 3. Why conservation does not retain the signed observable

### The complete cofactor-integer graph is not the lower LPF graph

Write `Q(n)=n/P(n)`. For every `n>=3`,

```
s(n)=-sgn(Q(n+1)-Q(n)).                                   (12)
```

Indeed, in `ap+1=bq`, `a>b` implies `q>p`, and `a<b` implies `q<p`. If `a=b`, then `a(q-p)=1`, so the only prime-to-prime exception is `n=2`; `n=1` is the other convention-dependent exception.

Equation (12) is not a Euclidean pushforward to another adjacent integer pair. It is a comparison in the graph of the **integer cofactors**, whose edges usually are not consecutive integers. Factoring an integer cofactor does not preserve this comparison: `5<6`, but every prime factor of 6 is less than 5.

This cofactor graph itself has only `o(X)` distinct vertex labels up to position `X`. To see this, fix `Y`: a label `a=Q(n)> (X+1)/Y` has `P(n)<Y`, and hence `P(a)<Y`. Thus the number of labels is at most

```
(X+1)/Y + #{a<=X+1: P(a)<=Y}.
```

For fixed `Y`, the second term is `O_Y((log X)^(pi(Y)))=o(X)`. Letting `Y` tend to infinity proves the claim. Consequently its edges too can be decomposed into cycles plus an `o(X)` path. This is a legitimate cycle-level integer-label reduction, but it has not become the original LPF adjacency problem at a smaller scale.

### An actual zero-defect cofactor cycle with nonzero ordering current

The four actual edges with indices `7,8,9,10` give

```
Q(7),Q(8),Q(9),Q(10),Q(11) = 1,4,3,2,1.
```

This is a directed simple cofactor-integer cycle. Its source and target products both equal 24, so its full prime-valuation defect is **zero**, while its integer-ordering current is

```
+1-1-1-1=-2.                                             (13)
```

Thus on the space of cofactor cycles, **every norm of the net factor-inventory vector has a kernel containing nonzero ordering current**. This is not a failure peculiar to logarithmic weights. Retaining only that vector, even with complete factorization, loses the observable.

A similarly literal example already occurs for closed prime walks. The dyadic walks for `N=3` and `N=5` have

```
N=3: prime word (3,2,5,3),       W(3)=-1,   D=e_2;
N=5: prime word (5,3,7,2,3,5),   W(5)=+1,   D=e_2.          (14)
```

The factor defects are identical but the ordering currents are opposite. The second walk need not be simple; it decomposes into genuine simple cycles as in Section 1.

There is a stronger certificate using two **simple prime cycles** of equal length:

```
C_minus: 5 -> 3 -> 13 -> 7 -> 5,  edges (5,12,13,14), W=-2;
C_zero:  5 -> 11 -> 3 -> 7 -> 5,  edges (10,11,6,14), W=0.
```

For both cycles, `r=4`, `A=8`, and `B=12`. Indeed their cofactor lists are respectively

```
C_minus: a=(1,4,1,2), b=(2,1,2,3);
C_zero:  a=(2,1,2,2), b=(1,4,1,3).
```

Thus the **complete source prime-factor inventories and complete target prime-factor inventories separately agree**, not just their difference. The signed cycle chain `Z=C_minus-C_zero` has zero prime-vertex boundary, zero total edge coefficient, and zero source and target factor inventories, but `W(Z)=-2`. Consequently no norm or linear functional of those inventories and total edge mass can retain the ordering current on signed cycle chains. This is a literal arithmetic certificate; it is not an abstract graph realization.

These examples rule out an exact recovery of ordering current from the net defect alone. They do not refute an asymptotic estimate for the particular complete dyadic walks; establishing such an estimate is the original problem.

### Adding a lower prime graph needs information not supplied by conservation

A factor inventory specifies supplies and demands, not their pairing. Two flows with the same boundary can differ by a circulation. Even with exactly the same source and target masses at the three primes `2,3,5`, diagonal matching has ordering current zero, the matching

```
2 -> 3 -> 5 -> 2
```

has current `+1`, and its reversal has current `-1`. The analogous freedom persists with logarithmic masses by moving a common amount no larger than the three available masses.

Therefore gluing cofactor-factor demands to supplies using (5) can produce a lower-scale circulation, but neither its ordering current nor its agreement with (2) follows from the gluing. A successful construction must prescribe and analyze the pairing using additional arithmetic edge information.

## 4. The high-sector positive mass contraction is real, but is not a signed descent

For one prime cycle put

```
M_prime = sum_i (log p_i+log p_(i+1)) = 2 sum_i log p_i,
M_cofactor = log A_Gamma+log B_Gamma.
```

If every edge has `n_i+1<=X+1` and every vertex has `p_i>=(X+1)^c`, then

```
M_cofactor+M_prime <= 2r log(X+1),
M_prime >= 2rc log(X+1),
M_cofactor <= ((1-c)/c) M_prime.                          (15)
```

For `c>1/2`, this is indeed a strict contraction of **positive logarithmic incidence mass**. Also `||D_Gamma||_log<=M_cofactor`.

The failures are not in (15). They are that:

* `D_Gamma` is a boundary/inventory, not a signed circulation carrying `W(Gamma)`;
* factorization does not preserve the integer-cofactor ordering in (12);
* the induced high-prime graph need not be balanced, so full cycles need not stay in this sector;
* arbitrary re-pairing into a lower prime graph need not yield the adjacent-LPF law under ordinary counting at any smaller integer scale.

Consequently (15) does not imply a contraction for the limsup of the natural bias. The next section shows that extending this particular logarithmic-mass contraction uniformly to all genuine prime cycles is false.

## 5. Genuine same-scale directed cycles with no logarithmic factor-norm saving

### Theorem

Fix an integer `r>=3` and `eta>0`. There are arbitrarily large `H` and actual directed simple prime cycles `Gamma` of length `r`, all of whose integer edge indices lie in

```
[H,(1+eta)H],
```

such that

```
W(Gamma)=2-r,
P(n_i),P(n_i+1) = Theta(sqrt H),
B_Gamma/A_Gamma = 1+Theta(1/H),
gcd(A_Gamma,B_Gamma)=O(1),                                (16)

||D_Gamma||_log / M_prime -> 1,
||D_Gamma||_log / log H -> r.                             (17)
```

Constants may depend on the fixed construction. In particular the factor-defect norm in (17) is **after** complete cancellation of common prime powers.

Thus no inequality

```
||D_Gamma||_log <= c M_prime + o(M_prime),  c<1,            (18)
```

can hold uniformly for all genuine directed cycles. Also

```
|W(Gamma)| / (||D_Gamma||_log/log H) -> 1-2/r,             (19)
```

which can be made arbitrarily close to 1 by fixing a sufficiently large `r`.

### 5.1 A family of slopes with controlled parity and differences

Construct finite increasing sets of positive integer slopes with

```
gcd(a,b)=b-a       for a<b,
v_2(a)>v_2(b)     for a<b.                               (20)
```

Start from `{1}`. If `S` has these properties, choose `M` divisible by every element of `S` and every nonzero pairwise difference, with `v_2(M)>max_{s in S} v_2(s)`. Then

```
{M} union {M+s:s in S}
```

again satisfies (20). For the old pairs, the difference divides both new values, so is their gcd; for a pair `M,M+s`, the gcd is `s`. The valuation assertion follows from `v_2(M+s)=v_2(s)`.

The last `M` can be made arbitrarily large. Write the final slopes as

```
M+s,  s in T={0} union S_old,  0<=s<=D.
```

Require, in addition,

```
M>2D^2,
(max slope/min slope)^2 < 1+eta.                          (21)
```

The slopes can therefore be as close in relative size as desired. Their strictly decreasing 2-adic valuations also exclude any three-term arithmetic progression: if `v_2(a)>v_2(a+d)`, then `v_2(d)=v_2(a+d)`, whereas `v_2(a+2d)>v_2(a+d)`.

For a pair of slopes `a<b`, put

```
d=b-a=gcd(a,b),    v=a/d,    u=b/d.
```

Then

```
u=v+1,    v even,    u odd.                              (22)
```

### 5.2 The only analytic input: a fixed-linear-form prime theorem

For the prescribed `r`, take sufficiently many slopes so that Maynard's theorem for admissible linear forms gives infinitely many `t` with at least `r` of

```
a t+1
```

prime. This family is admissible: `t=0` modulo any prime avoids that prime in every form. The slopes are fixed constants, and the forms are distinct and primitive. After passing to an infinite subsequence, select a fixed `r`-element slope subset

```
c_1<...<c_r,    p_i=c_i t+1 all prime.
```

The input is Maynard, *Dense clusters of primes in subsets*, arXiv:1405.2593, theorem labelled `thrm:ShortIntervals` in the local source `/corpus/src/1405.2593/Subsets.tex`, taking `m=r`, `y=x`, and any fixed permissible epsilon, e.g. `1/10`. Its coefficient bound holds eventually for every fixed slope. It asserts at least `r` prime values among sufficiently many forms, **not** the unproved simultaneous primality of an arbitrary prescribed small tuple.

### 5.3 Two genuine directions near the same product

For `p=a t+1`, `q=b t+1` from a slope pair, (22) gives

```
u p-v q=1.                                               (23)
```

For large `t`, the following are actual LPF edges:

```
q -> p at n_down=(p+v)q,       n_down+1=(q+u)p;
p -> q at n_up  =(q-u)p,       n_up+1  =(p-v)q.             (24)
```

To verify the largest-prime conditions, use `q<2p` for large `t`:

* `p+v<q`;
* `q+u` is even and `(q+u)/2<p`;
* `q-u` is positive and even, with `(q-u)/2<p`;
* `0<p-v<p<q`.

Thus all complementary factors have prime factors below the declared largest prime. Both edge indices are `pq+O(t)`, not one edge at scale `t` and the other at scale `t^2`.

Use the downward edge in (24) for each

```
p_r -> p_(r-1) -> ... -> p_1,
```

and the upward edge for `p_1 -> p_r`. This gives a directed simple cycle with `r-1` descents and one ascent, hence current `2-r`. The edges are distinct because their source LPF labels are distinct. By (21), all edge indices lie in a fixed relative interval of ratio less than `1+eta` for large `t`; let `H` be their minimum. They are all `Theta(t^2)`, proving the first size assertions in (16).

For this cycle, the cofactor products are products of the following linear polynomials:

```
A: c_(j-1)t+1+c_(j-1)/(c_j-c_(j-1))   (2<=j<=r),
   c_r t+1-c_r/(c_r-c_1);

B: c_j t+1+c_j/(c_j-c_(j-1))           (2<=j<=r),
   c_1 t+1-c_1/(c_r-c_1).                               (25)
```

Each product is asymptotic to `(prod_i c_i)t^r`. Equation (3) gives `B/A=1+Theta(t^(-2))`.

### 5.4 All common cofactor factors are bounded: a resultant argument

No polynomial in the `A` list is proportional to a polynomial in the `B` list.

For the first `r-1` polynomials, their roots have the form

```
-1/d-1/c,
```

where `d` is a positive slope gap, `d<=D`, and `c>=M`. If two gaps differ, their reciprocal difference is at least `1/D^2`, whereas the difference of the `1/c` terms is less than `1/M`; (21) prevents equal roots. If the gaps agree, equal roots require the same slope. Across the `A` and `B` lists, that would give an interior slope whose two neighboring gaps agree, a three-term arithmetic progression excluded by (20).

The last polynomial in each list has a positive root, so cannot share a root with the preceding polynomials. The two last roots are

```
1/(c_r-c_1)-1/c_r,    1/(c_r-c_1)-1/c_1,
```

and are distinct.

For fixed integer linear polynomials `alpha t+beta` and `gamma t+delta` with different roots, their integer values have gcd dividing the nonzero constant

```
alpha delta-beta gamma.
```

It follows, by taking the product of these constants over all cross pairs in (25), that

```
gcd(A(t),B(t)) <= C                                      (26)
```

for a fixed finite constant `C`. Formally, prime by prime,
`gcd(prod_i A_i,prod_j B_j)` divides `prod_{i,j} gcd(A_i,B_j)`, and each pair gcd divides its resultant.

Now (7), (25), and (26) give

```
||D_Gamma||_log=2r log t+O(1),
M_prime=2r log t+O(1),
log H=2 log t+O(1),
```

proving (17)-(19).

### A small numerical certificate

This is a finite illustration, not the prime-producing input above. With slopes `(12,14,15)` and `t=50`, all three values are prime:

```
p=601, q=701, r=751.
```

The cycle is

```
751 -> 701: 715*751+1 = 766*701,   n=536965;
701 -> 601: 607*701+1 = 708*601,   n=425507;
601 -> 751: 746*601+1 = 597*751,   n=448346.
```

The actual cofactor factorizations verify the LPF labels:

```
715=5*11*13, 766=2*383,
607 prime,  708=2^2*3*59,
746=2*373,  597=3*199.
```

Here

```
A=323767730, B=323769816, gcd(A,B)=2,
B-A=2086, W=-1.
```

For these fixed slope polynomials the identity is `B(t)-A(t)=41t+36`, and all cross resultants are nonzero. The general theorem does not assume that this particular triple is simultaneously prime infinitely often.

### Scope of this obstruction

The construction has `p_i=Theta(sqrt H)`. Prefix class multiplicities are `Theta(sqrt H)`, so this is not the bounded-degree, primes-near-`X` obstruction to the earlier untrimmed skew operator norm. Nevertheless these are sparse constructed cycles, not a positive-density portion of the full interval. Opposite-direction edges are also available in (24), so favorable inter-cycle pairings are not excluded.

In particular:

* (18) is genuinely false as a uniform statement on all directed arithmetic cycles;
* the family does not refute (15) for a fixed `c>1/2`;
* it does not prove that every cycle decomposition of a full interval fails;
* it does not refute `W(N)=o(N)`.

## 6. What a successful new descent would still have to supply

After (5), demanding better marginal balance at the lower prime level cannot be the missing step: the complete dyadic inventory is already exactly `e_2`. Its associated boundary has only constant logarithmic mass.

The missing data are the **signed pairing and circulation**, not the total supplies. A successful argument must retain enough of the original edge/cofactor incidence to do at least one of the following:

* pair different cycles' factor demands so that the unmatched **ordering current**, not merely the unmatched factor inventory, is `o(N)`; or
* produce a lower-scale signed edge-chain in a class to which the same natural-density limsup applies, with a proved contraction and an `o(N)` ordering error.

Section 3 shows why passing only to the defect vector cannot do this. Section 5 shows why a uniform logarithmic-incidence saving on individual arithmetic cycles cannot be taken for granted. Section 4 identifies the restricted positive-mass contraction that is valid, and the precise extra properties it lacks.

No such sign-compatible inter-cycle estimate or closed class of lower-scale laws was obtained here. In particular there is **no** established inequality `|limsup bias|<=c|limsup bias|` with `c<1`, and no `o(X)` remainder for the original ordering sum. The `o(X)` result (11) concerns only an inventory boundary. This distinction prevents mass conservation from being mistaken for a solution of the natural-density problem.

## Verification

`CycleCofactorVerification.py` uses ordinary integer arithmetic, a largest-prime-factor sieve, signed valuation counters, gcds, and resultants. It checks:

* cofactor order reversal and square-root support up to 600,001;
* exact dyadic cycle decompositions, genuine edge partitions, and total defect `e_2`;
* individual product identities, reduced prime-factor norms, and (9);
* full-prefix residual-path logarithmic bounds;
* the zero-defect cofactor cycle, the equal-defect/opposite-bias prime walks, and two simple prime cycles with identical source/target factor inventories but different currents;
* the directed high-prime triangle `11 -> 17 -> 13 -> 11` at edge indices `33,51,65`, whose products are `45,48`;
* the numerical same-scale cycle above and its cofactor polynomial gcd certificates;
* the slope recursion through six slopes and every subset-cycle system of length at least three, including nonzero cross resultants.

The output is in `CycleCofactorVerification.log`. Finite tests verify these algebraic claims, not the asymptotic theorem about primes. That theorem's analytic input is the explicitly identified fixed-linear-form result of Maynard; the rest of its proof is given above.
