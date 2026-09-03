# Two-center WR investigation: sharper absorption and a genuine cap-tail obstruction

## Status

**WR is neither proved nor disproved here.** No asymptotic divergence of
`B²/(n²+R)` has been established. No sharp distinct-distances theorem follows,
and no Lean files were edited. The results below are new to this investigation;
no claim of historical priority is intended.

There are three concrete findings:

1. A direct endpoint-pair charge improves the one-center reduction to
   `B <= 2 H_1 + n`, with a sharp additive `n`. More generally it absorbs
   witnesses whose full pinned fiber is much larger than their axis occupancy.
2. A genuine planar family has `D=o(n)`, `m -> infinity`,
   `w/m² -> infinity`, and axis mass `h_l=(1-o(1))m` simultaneously. Thus
   two-center injectivity, even with the **actual global palette and full
   fibers**, cannot impose a vanishing per-axis mass discount as the cap
   becomes more active.
3. More strongly, rectangular integer grids have a positive fraction of `B`
   on axes with both `m -> infinity` and `w/m² -> infinity`. This mass is
   `omega(n)`. Hence the overfull-axis tail cannot simply be absorbed into
   `O(n)`, or uniformly into `epsilon(T) B + O_T(n)` with `epsilon(T)->0`.

The last two statements obstruct natural ways of inserting the cap; neither
**establishes a counterexample to WR**. Exact two-center incidence/entropy
identities are also recorded, retaining the full pinned-fiber denominators
throughout.

## 1. Normalization and a sharper non-Cauchy absorption

Assume `n>=2`, so the positive squared-distance palette `S` has `D>=1` elements.
Put

    s_P = (sum_p d_p)/D <= n,
    B = n(n-1)/D - s_P.

Every ordered isosceles witness `(p,a,b)`, with distinct endpoints and
`|p-a|²=|p-b|²=s`, has weight `1/(D k_{p,s})`. Its bisector axis is denoted `l`.
Write `h_l` for the mass on that axis; then `sum_l h_l=B`.

### Proposition 1: joint fiber/occupancy absorption

For any real `lambda>1`, let `J_lambda` be the mass on witnesses satisfying

    k_{p,s} >= lambda m_l,

and let `K_lambda=B-J_lambda`. Then

    J_lambda <= n(n-1)/(lambda D) = (B+s_P)/lambda,
    B <= lambda/(lambda-1) K_lambda + s_P/(lambda-1).       (1.1)

**Proof.** Fix an ordered endpoint pair `(a,b)` whose bisector has `m>=1`
actual centers. At each qualifying center its weight is at most
`1/(lambda D m)`. There are at most `m` such centers, so this ordered pair
receives total charge at most `1/(lambda D)`. There are `n(n-1)` ordered
endpoint pairs in total. Rearrangement proves (1.1). Pairs with no actual
centers receive no charge. No Cauchy--Schwarz step is involved. QED.

For `lambda=2`, every one-center witness qualifies, since its full fiber has
at least two endpoints. Therefore, with `H_1` the mass on axes with `m>=2`,

    B <= 2 K_2+s_P <= 2 H_1+n,
    B² <= 8 H_1²+2n².                                    (1.2)

The additive `n` in the first inequality cannot be decreased uniformly: a
regular odd polygon has `D=d_p=(n-1)/2`, all its occupied bisectors have one
actual center, and `B=n`. An equilateral triangle already gives equality.

The stronger information in (1.1) is a joint restriction: after a constant
loss, it suffices to retain witnesses with `k_{p,s}<lambda m_l`, not merely
axes with many centers. It does not by itself justify the cap on `w_l`.

## 2. Exactly what two centers determine

Fix an axis, use Euclidean coordinates in which it is the horizontal axis,
and let its actual centers have coordinates `t in T`, `|T|=m`. Its unordered
nonfixed reflected pairs form a set `A` of size `q=w/2`. Represent a pair by
`(x_a,+y_a),(x_a,-y_a)` with `y_a>0`, and put

    f_a(t) = (x_a-t)²+y_a²,
    g_a(t) = f_a(t)-t² = -2 x_a t+x_a²+y_a².

The `g_a` are distinct lines. Define

    r_{t,s} = #{a in A : f_a(t)=s},
    b_t = #{s : r_{t,s}>0},
    z_t = (1/D) sum_{s:r_{t,s}>0} 2r_{t,s}/k_{t,s}.

Thus `h_l=sum_t z_t`. Always `2r_{t,s}<=k_{t,s}` and `0<=z_t<=1`.

### 2.1 Injectivity and the full-fiber deficit

For `t!=u`, the map

    a -> (f_a(t),f_a(u)) in S x S                         (2.1)

is injective: subtracting the two evaluations determines `x_a`, and then
one evaluation determines `y_a²`. The two-center table is consequently a
simple bipartite graph with `q` edges, row degrees `r_{t,s}`, and column
degrees `r_{u,v}`. In particular,

    q <= b_t b_u <= D².                                  (2.2)

Also, two distinct lines `g_a,g_b` agree at at most one center, so

    sum_{t in T} sum_s binom(r_{t,s},2) <= binom(q,2).     (2.3)

It is essential not to replace `k` by `2r`. Set

    c_{t,s}=k_{t,s}-2r_{t,s}  (on labels with r_{t,s}>0).

Then exactly

    b_t-D z_t = eta_t,
    eta_t = sum_{s:r>0} c_{t,s}/(2r_{t,s}+c_{t,s}),
    0 <= eta_t <= (n-1-w)/3.                             (2.4)

Indeed, `sum_{r>0} c_{t,s}<=n-1-w`. If `c>0`, the integer denominator
`2r+c` is at least three, so `c/(2r+c)<=c/3`. When the set is invariant
under reflection in this axis, all unmatched endpoints are actual fixed
centers, and (2.4) improves to `eta_t<=(m-1)/3`.

### 2.2 Exact entropy and inverse-fiber identities

Choose `a` uniformly from the `q` reflected pairs. Let `X=f_a(t)`,
`Y=f_a(u)`. All logarithms below are natural; sums over `a` run over `A`.
Injectivity gives the exact identity

    I(X;Y) = log q - (1/q) sum_a log(r_{t,f_a(t)} r_{u,f_a(u)}).   (2.5)

For the full pinned distributions

    mu_t(s)=k_{t,s}/(n-1),   mu_u(v)=k_{u,v}/(n-1),

let `pi` be the joint distribution of `(X,Y)`. Its nonzero entries are
`1/q` on the simple edge set (2.1). Consequently,

    KL(pi || mu_t x mu_u)
       = 2log(n-1)-log q
         -(1/q) sum_a log(k_{t,f_a(t)} k_{u,f_a(u)}),       (2.6)

and, with the usual chi-square divergence,

    1 + chi²(pi || mu_t x mu_u)
       = (n-1)²/q² sum_a 1/(k_{t,f_a(t)} k_{u,f_a(u)}).    (2.7)

Zeros of the reference measure cause no problem: a positive entry of `pi`
has both full fiber sizes at least two. Formula (2.6) also decomposes as
`I(X;Y)+KL(pi_X||mu_t)+KL(pi_Y||mu_u)`.

For clarity about the change of averaging, put
`theta_{t,a}=2r_{t,f_a(t)}/k_{t,f_a(t)}`. Then another exact form is

    (1/q) sum_a log(k_{t,f_a(t)} k_{u,f_a(u)})
       = log(4q)-I(X;Y)
         -(1/q) sum_a log(theta_{t,a} theta_{u,a}).        (2.8)

These are identities, not a closing entropy estimate. In particular `z_t`
is a **uniform-palette** sum of the reflected fractions, whereas (2.5)--(2.8)
use **uniform reflected pairs**. Injectivity gives lower bounds for support
and nonnegative divergences; it does not automatically give the upper bound
for `h_l` that would insert the cap.

For comparison, ordinary real ST on the `q` lines `g_a` and the points
`(t,s-t²)` with `r_{t,s}>0` gives

    qm <= C[(q sum_t b_t)^(2/3)+q+sum_t b_t].

Using `sum b_t<=mD`, (2.2) for bounded `m`, and `D>=m-1` from the actual
collinear centers, this implies `mq=O(D²)` for `m>=2`. This familiar local
incidence restriction is fully compatible with both examples below.

## 3. An actual axis can be asymptotically saturated far beyond the cap

### Theorem 2: full-palette local cap-discount obstruction

For integers `L->infinity`, put `m=floor(sqrt L)` and

    P_L = {0,...,L}² minus {(j,j): m<=j<=L}.

Let `l` be the diagonal `x=y`. With the original global palette, full pinned
fibers, and ordered reflection count, one has

    n=L(L+1)+m,       w_l=L(L+1),
    D(P_L)=o(n),      B(P_L)/n -> infinity,
    m_l=m -> infinity,
    w_l/[m_l(m_l-1)] ~ L -> infinity,
    h_l/m_l -> 1.                                      (3.1)

Thus no universal estimate

    h_l <= C m_l epsilon(w_l/[m_l(m_l-1)])

with `epsilon(t)->0` can hold, even restricted to genuine sets with `D=o(n)`
and axes with an unbounded number of actual centers.

### Proof with a finite quantitative bound

Let

    S_L={x²+y²: 0<=x,y<=L, (x,y)!=(0,0)},    N_L=|S_L|.

Since all differences of points of `P_L` have coordinate absolute values at
most `L`, the actual global palette is contained in `S_L`. Conversely, the
pin at `(0,0)` realizes every element of `S_L` except possibly the at most
`L` values represented only by removed diagonal points. Hence

    N_L-L <= D(P_L) <= N_L.                              (3.2)

Reflection in `x=y` preserves all of `P_L`. Its nonfixed points are exactly
all the `L(L+1)` off-diagonal grid points, proving the formulas for `n,m,w`.

At the actual center `p_j=(j,j)`, `0<=j<m`, the points

    p_j+(x,y),  0<=x,y<=L-j,  x!=y

and their reflections all belong to `P_L`. Therefore the reflected-label
support satisfies

    b_j >= N_{L-j}-(L-j)
        >= N_L-2j(L+1)-L.                               (3.3)

For the second inequality, deleting the outer coordinate strips removes at
most `(L+1)²-(L-j+1)²<=2j(L+1)` possible vector representatives.

The only unpaired points in a full pinned fiber are among the other `m-1`
actual diagonal centers. By (2.4), `D z_j>=b_j-(m-1)/3`. Together with
`D<=N_L`, and the trivial `z_j>=0` if the following lower bound is negative,
this gives

    z_j >= 1-[2j(L+1)+L+(m-1)/3]/N_L.

Sum over `j` and divide by `m`:

    1 >= h_l/m >= 1-[L m+(4/3)(m-1)]/N_L.                (3.4)

The elementary bounds in Appendix A give

    N_L=o(L²),     N_L>=L²/(12+8log L).

Thus the error in (3.4) is `O(log L/sqrt L)=o(1)`. Equations (3.1) follow,
using `B/n >= (n-1)/D-1`. The same argument works for any integer
`m->infinity` with `m log L=o(L)`. QED.

The contribution of this one axis to `R` is `m²(m-1)`, so
`h_l²/R_l~1/m`, not a divergent ratio. The theorem obstructs a **local mass
discount**, not WR. Its large mass is still a small fraction of total `B`.
The next theorem addresses that last limitation.

## 4. Arbitrarily overfull rich axes can carry a fixed fraction of total B

### Theorem 3: the overfull-axis tail is not absorbable

There exist integer rectangular grids `P_L`, parameters `M_L->infinity`,
`T_L->infinity`, and an absolute `c>0`, such that

    D(P_L)=o(n_L),
    sum_{l: m_l>=M_L, w_l>=T_L m_l²} h_l
          >= c n_L²/D(P_L) >= c B(P_L).                  (4.1)

In particular, the mass on the left is `omega(n_L)`.

One concrete choice is

    H=floor[L/(log L)^(1/8)],
    P_L={-L,...,L} x {-H,...,H},
    A=L/H,
    M_L=floor[(log L)^(1/8)],    T_L=A/2304,              (4.2)

for all sufficiently large `L`. The use of the classical sum-of-two-squares
upper bound in this particular parameterization can be avoided; see 4.4.

### 4.1 A uniform arithmetic-geometric overlap lemma

Let `L>=H`, and suppose an axis passes through an actual point

    |p_x|<=L/8,     |p_y|<=H/8

and has primitive integer direction `v=(a,b)`, `b>0`, satisfying

    L |a| <= 8H b.                                      (4.3)

If its actual occupancy is `m>=65`, then

    w >= (L/H) m²/2304.                                 (4.4)

**Proof.** Set `t=H/b`. Since the axis contains the lattice point `p` and
`v` is primitive, all its integer points are `p+r v`, `r in Z`. Hence
`m<=2t+1`, and `m>=65` implies `t>=32`.

Let `v_perp=(-b,a)`, and set

    R0=floor[H/(16b)],     S0=floor[L/(16b)].

All the points

    p+r v+s v_perp,  |r|<=R0, |s|<=S0

belong to the rectangle. Indeed their coordinate displacements are at most

    R0|a|+S0 b <= 8H²/(16L)+L/16 <= 9L/16,
    R0 b+S0|a| <= H/16+8H/16 = 9H/16,

and the bulk-center allowance adds only `L/8,H/8`. Reflection in the axis
maps `(r,s)` to `(r,-s)`. Every point with `s!=0` is a distinct nonfixed
reflected endpoint, so

    w >= (2R0+1) 2S0
      >= (t/16)((L/H)t/16)
      = (L/H)t²/256
      >= (L/H)m²/2304.

The floor estimates use `t>=32`, and `m<=3t` gives the last inequality.
The count `w` is ordered, since it counts each nonfixed endpoint once.
QED.

### 4.2 A fixed fraction of witness mass lies in the near-vertical cone

Take `A=L/H>=16`, and consider every actual center in the bulk rectangle

    C={p: |p_x|<=L/8, |p_y|<=H/8}.

At such a center restrict to full pinned fibers with

    L²/16 <= s <= L²/4.                                 (4.5)

Reflection in the vertical line through `p` preserves each of these entire
fibers: its horizontal offsets have absolute value at most `L/2`, and both
signs lie inside the horizontal range of `P_L`. None has horizontal offset
zero, since its vertical offset has absolute value at most `9H/8<L/4`.
Thus a full fiber of size `k` has exactly `k/2` endpoints to the left and
`k/2` to the right of `p`.

Its ordered opposite-side witnesses have total normalized mass

    [2(k/2)²]/(Dk) = k/(2D).                             (4.6)

This is an exact full-fiber identity, not an estimate using a subfiber.
Moreover each such witness has a near-vertical bisector satisfying (4.3).
Indeed (4.5) and `A>=16` imply that each endpoint's horizontal offset has
absolute value greater than `L/8`. Opposite-side endpoints therefore have
horizontal separation at least `L/4`, while their vertical separation is
at most `2H`. A direction perpendicular to their difference satisfies
`|a|/b<=8H/L`.

There are `Omega(n)` bulk centers. At every one of them (4.5) contains
`Omega(n)` endpoints: for example take both signs of the integer horizontal
offsets in `[L/3,2L/5]` and all integer vertical offsets in `[-H/2,H/2]`.
These lie in `P_L` and satisfy (4.5). Consequently the mass `E` of all these
opposite-side witnesses satisfies, for an absolute `c0>0`,

    E >= c0 n²/D.                                      (4.7)

For explicit finite constants, when `L>=30`, `H>=16`, and `A>=16`, the
above choices give at least `LH/64` centers and `LH/15` endpoints per
center. Since `n<=9LH`, one can take `c0=1/155520`.

### 4.3 Removing small occupancies does not remove this mass

The previously verified low-center estimate gives

    L_M² <= M n²(n-1)/D.                                (4.8)

For (4.2), every squared distance is a sum of two integer squares at most
`8L²`. The classical Landau--Ramanujan upper bound gives

    D=O(L²/sqrt(log L)),
    D/n=O((log L)^(-3/8)),
    M_L D/n=O((log L)^(-1/4)) -> 0.                      (4.9)

By (4.7)--(4.8),

    (L_{M_L}/E)² <= M_L D/(c0² n) -> 0.

For large `L`, at least `E/2` of the selected witness mass remains on axes
with `m>=M_L>=65`. Those axes have an actual bulk center and satisfy (4.3),
so (4.4) places all of them in the family in (4.1). We obtain (4.1) with,
for example, `c=c0/2`. Also `n/D->infinity`, proving that this mass is
`omega(n)`. QED.

A precise consequence is the failure of **every** proposed uniform estimate

    sum_{l:m_l>=2, w_l>=T m_l²} h_l
        <= epsilon(T) B + C_T n,
    epsilon(T) -> 0,                                    (4.10)

with finite constants `C_T`. Choose a fixed `T` for which `epsilon(T)<c/2`,
and then let `L->infinity` in (4.1); eventually `T_L>=T` and `n=o(B)`.
This contradicts (4.10). In particular, `O_T(n)` absorption alone is false.

This argument never asserts that `R` is small. The many other axes and the
capped contributions of the selected axes remain part of the original WR.
Theorem 3 supplies no divergence of its ratio.

### 4.4 An elementary parameter choice without a Landau asymptotic

Let `U(X)` count positive integers at most `X` that are sums of two integer
squares. Appendix A proves `U(X)=o(X)`. Set

    epsilon_L=U(8L²)/L²,
    A0=epsilon_L^(-1/4),
    H=floor(L/A0),      M_L=ceil(A0).

Then `epsilon_L->0`, `A=L/H~A0->infinity`, and `H->infinity` (already
`U(8L²)>=floor(sqrt(8)L)` implies `A0=O(L^(1/4))`). Furthermore

    D/n=O(epsilon_L^(3/4)),
    M_L D/n=O(epsilon_L^(1/2))->0.

Thus the same proof gives Theorem 3, with `T_L=A/2304`, using only the
elementary density-zero fact. This is also a concrete, finite-count-defined
sequence of genuine integer rectangles.

## 5. What remains missing

The two-center graph is genuinely injective, its lines are real lines, all
its labels belong to the actual global palette, and the denominators in
(2.4)--(2.8) are the full pinned fibers. The obstructions above retain all
of these properties.

Nevertheless:

* (1.1) only absorbs witnesses with `k` large compared with `m`.
* (2.2)--(2.8) give local support, collision, and divergence information, not
  an upper bound for the total mass over many axes.
* Theorem 2 prevents inserting the cap by reducing an individual axis's
  mass by a factor tending to zero with `w/m²`.
* Theorem 3 prevents disposing of all strongly overfull axes as an `O(n)`
  error, or as a uniformly vanishing fraction of `B` plus such an error.

These are not impossibility results for every use of the complete collection
of two-center data. They rule out exactly the per-axis discounts and tail
absorptions stated above. A valid closing argument would have to use more
than those effects: for example, an actual inequality coordinating mass and
capped budgets across different axes. No such inequality is proved here.
No equivalent reformulation is being offered as a solution. Universal WR
and the sharp planar distinct-distances bound remain unresolved.

## Appendix A. Elementary number-theoretic inputs for Theorem 2 and 4.4

### A.1 A lower bound for the square's norm support

Let `E_L` count ordered pairs of vectors in `{0,...,L}²` with equal squared
norm. The pairs with equal first coordinates are identical vectors, giving
`(L+1)²` choices. Otherwise, after choosing one of two orientations, set

    a=x1-x2>0, b=x1+x2,
    c=y2-y1>0, d=y2+y1.

The norm equality is `ab=cd`, with `a,c<=L` and `b,d<=2L`. Write
`a=g u,c=g v`, `gcd(u,v)=1`, `h=max(u,v)`. Then `b=v t,d=u t`, and

    g<=L/h,       t<=2L/h.

There are at most `2h` ordered coprime pairs `(u,v)` with maximum `h`.
Ignoring parity and endpoint constraints only enlarges the count. Hence

    E_L <= (L+1)²+8L² sum_{h=1}^L 1/h
        <= L²(12+8log L).

There are `(L+1)²-1>=L²` nonzero vectors. Cauchy--Schwarz on their norm
representation counts gives

    N_L>=L²/(12+8log L).

This use of Cauchy is just an elementary arithmetic support estimate for an
explicit example; it is not being presented as a new WR closing step.

### A.2 Sums of two squares have density zero

For every prime `p=3 mod 4`, a sum of two integer squares divisible by `p`
is divisible by `p²`. Thus it avoids the `p-1` residue classes of valuation
exactly one modulo `p²`. For any fixed finite collection `F` of such primes,
CRT gives the upper density bound

    limsup_{X->infinity} U(X)/X
       <= product_{p in F}(1-1/p+1/p²).

The reciprocal sum of primes `3 mod 4` diverges, so these products tend to
zero as `F` increases. For completeness, the divergence follows by comparing
Euler-product logarithms for `zeta(s)` and `L(s,chi_4)` as `s->1+`:
`log zeta(s)` diverges, `log L(s,chi_4)` stays bounded because
`L(1,chi_4)=pi/4`, and the prime-power terms beyond the first are uniformly
bounded. Their difference is `2 sum_{p=3 mod 4} p^(-s)+O(1)`.
This proves `U(X)=o(X)` and consequently `N_L=o(L²)`.

## Verification and file integrity

The reproducible command is

    python3 Submission/verify_wr_two_center_cap_obstruction.py

Its output is in `Submission/wr_two_center_cap_obstruction_verification.txt`.
The checks use integer coordinates, three positive-definite integral Gram
matrices, exact rational weights, direct full pinned supports, and actual
reflected pairs. They test the sharpened absorption, full-fiber deficit,
two-center injectivity, collision bound, and chi-square identity on all
1,506 subsets of a 3-by-3 coordinate box with at least two points in those
three metrics. Separate tests check five punctured grids, the exact
opposite-side mass identity in three small rectangles and at six bulk pins
in larger rectangles, and six reflection sublattice counts by direct rational
reflection. The arithmetic support/energy bounds are independently checked
for `L=1,...,100`. All checks passed. Finite checks verify implementations
and finite identities, not asymptotic claims or universal WR.

No Lean files were modified. The SHA-256 of `Submission/Spec.lean` remains

    c2fbaabe5ad8088f856ca97625747c7a01754f3c149dd6a493454e776de290db
