# Epsilon-enlarged BV continuation: finite-tuple completion and the overlap test

## Status

This continues `GlobalBandPOVMAudit.md`, which was read in full. **The requested globally compatible completion is not established here, and there is no honest arithmetic separation or proof of Erdős #5.** There is, however, a uniform positive operator result for every *individual* finite tuple, not merely a scalar feasibility check:

> For every `0<a<b<2a`, `p=a/(a+b)`, and `p<R=(1+eps)/4<1/2`, the actual truncated BV forms on `H_A=L²(Delta_A(R))` admit a positive exact-pattern completion for every finite A. The completion can preserve the entire original stripe POVM on the coordinate-capped part of that simplex, and hence preserves all the required ordinary-support data. The Naimark lifting inequality has a dimension-independent strictly positive margin.

Consequently, **no test F in one tuple can separate just its own listed normalization, truncated-lower, ordinary-one-prime, forbidden-pair, and indicated ordinary higher-upper inputs.** Overlap constraints are not disposed of by this statement.

There are three further concrete results below:

* A direct formula independently constructs a positive fixed-tuple completion, including the required core/long cross terms. Its failure of the usual tensor marginal identity is calculated exactly: `-1/450` in a two-site example.
* A different, cylindrical construction works for *every two-site tuple*, including ordinary stripe pair data. Thus the first overlap difficulty is not simply the two-site compatibility of the actual lower bounds.
* For a specified induced 7-cycle, eight explicit remaining operator inequalities are displayed. A 15-dimensional simplex-supported compression passes, but their positivity on the entire Hilbert space is not proved. This is a concrete remaining finite operator test, not a claimed theorem.

`Spec.lean` was not edited or used as a proof source. Its checksum remains

```
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```

No Lean proof or admission is used.

## 1. Honest support ranges

Write

```
c=1/p,              2<c<3,
R=(1+eps)/4,        s=(1-eps)/4=1/2-R,
p<R<1/2,           0<s<1/6<p.
```

All functions are zero-extended when an integral leaves their support. Define

```
B_i F(t_-i) = 1_(sum t_-i <= s) integral F(t_i,t_-i) dt_i,
T_i = B_i* B_i,
I(F)=||F||².
```

The source `/corpus/src/1407.4897/newergap-submitted.tex`:

* lines 625ff state the epsilon-enlarged simplex theorem;
* lines 1333–1355 rescale its support and truncated functionals;
* lines 1363–1380 justify the denominator when `2R<1`;
* line 1386 expressly says that the available prime theorem does **not** give a full prime asymptotic on the enlarged support;
* lines 1388–1425 implement the truncated lower bound while retaining cross terms.

The 3.99 pair result in `/corpus/src/1811.03008/limitp2.tex`, lines 350–390, assumes total divisor support at most a small `delta`, with additional tuple/CRT hypotheses. It is not used on the enlarged support here. The model agrees with the ordinary stripe data on a larger ordinary subdomain, so it meets that pair bound wherever the source actually supplies it. The same statement applies to the stated scalar r-upper hierarchy `C_r >= 3^(r-1)` on its stipulated ordinary domains.

All arguments below are for complex Hilbert spaces and therefore preserve polarization and entangled tests, not just real nonnegative F.

## 2. Uniform fixed-tuple Naimark completion

### 2.1 Spaces and the prescribed core

Let

```
H = L²(Delta_A(R)),
H0 = L²(Delta_A(R) intersect [0,p]^A),
Gi = L²(Delta_(A\{i})(s)),
K = L²(phase u modulo a+b) tensor tensor_(i in A) L²(0,p).
```

Phase measure is normalized. Denote the stripe membership indicators by `chi_i(u)`. As in the preceding audit,

```
E chi_i=p,
sigma_ij=E(chi_i chi_j),
gamma_ij=sigma_ij/p².
```

On K take the commuting projections

```
Q_i = chi_i(u) Pi_i,       Pi_i=|1_(0,p)><1_(0,p)|/p.
```

Their joint spectral projections are `Q_D`, indexed by exact binary patterns. Forbidden patterns have zero projection. Embed H0 by the constant-phase isometry V0, using zero extension in the cube.

For `g in Gi`, define the isometry

```
U_i g(u,t) = chi_i(u)/p * 1_(0,p)(t_i) * g(t_-i).
```

Indeed, `||U_i g||²=p*p/p² ||g||²=||g||²`, and `range U_i` lies in `range Q_i`. Crucially,

```
U_i* V0 F = B_i F,                  F in H0.             (1)
```

The right side is the actual truncated integrator, not a full-J assertion on H.

### 2.2 The exact Gram inequality

Let `G=(U_i*U_j)_(i,j)` on the finite direct sum of the Gi, and let `B:H -> direct_sum Gi` have components B_i. Put `q_i(t_-i)=sum t_-i`.

The diagonal blocks are

```
G_ii=I,
(BB*)_ii=(R-q_i) I.
```

For different i,j, denote by `K_ij` the kernel taking the overlap of the two marginal lifts. The crucial support check is

```
2s<R.
```

If both `g_i(t_-i)` and `g_j(t_-j)` contribute, then `t_i,t_j<=s`, and their joint support has total at most `2s`. Therefore the enlarged simplex boundary does not truncate this overlap. Exactly,

```
G_ij=gamma_ij K_ij,
(BB*)_ij=K_ij.                                         (2)
```

To bound this matrix uniformly in the number of sites, set

```
W_i g(t)=1_(0,s)(t_i) g(t_-i),
```

viewed in a common `L²([0,s]^A)`. Then

```
W_i*W_i=s I,            W_i*W_j=K_ij  (i!=j).
```

The scalar matrix

```
C_ij=E[(chi_i/p-1)(chi_j/p-1)]
```

is positive semidefinite, has diagonal `c-1`, and off diagonal `gamma_ij-1`. Consequently the operator matrix

```
(C_ij W_i*W_j)_(i,j)
```

is positive: its quadratic form is

```
E_u || sum_i (chi_i(u)/p-1) W_i g_i ||².
```

Combining this with (2) gives the exact identity

```
G-BB*
 = (C_ij W_i*W_j)_(i,j)
   + diag_i [1-R+q_i-(c-1)s].                           (3)
```

In particular,

```
G-BB* >= kappa I,
kappa=1-R-(c-1)s = R+(3-c)s > R > 1/3.                  (4)
```

This is a solved operator inequality, with no dimension loss or ignored cross terms. For

```
a=1, b=3/2, p=2/5, R=9/20, s=1/20,
```

it gives `kappa=19/40`.

### 2.3 Contraction extension and exact patterns

On the linear span in K of `V0 H0` and the `U_i Gi`, prescribe

```
L(V0 f + sum_i U_i g_i) = f + sum_i B_i* g_i,             (5)
```

with H0 included in H. Equation (1) makes all mixed terms in the difference of squared norms cancel. That difference is precisely

```
<g,(G-BB*)g> >= 0.
```

Thus (5) is well-defined and contractive. Extend it continuously, and set it to zero on the orthogonal complement of its domain closure. Let `V=L* : H -> K`. Because `L V0 f=f` and L is a contraction,

```
V f=V0 f        for f in H0,
U_i* V=B_i.
```

Complete V to an isometry

```
Vhat F = V F direct_sum (I-V*V)^(1/2) F
```

into `K direct_sum H`. Give the second summand the all-nonprime outcome. Explicitly,

```
E_D = V* Q_D V,                                   D != empty,
E_empty = V* Q_empty V + I-V*V.                         (6)
```

These effects are positive, sum to I, and have forbidden-pair zeros. Since `U_i U_i* <= Q_i`,

```
E_i = V* Q_i V >= V* U_i U_i* V = B_i* B_i = T_i.        (7)
```

Compression to H0 is exactly the original stripe POVM. Hence its one-prime forms there are full J_i and its all-prime r-moments are `gamma(S) J_S`, with `gamma(S)<3^(r-1)` for r>=2. Every ordinary `total<=1/4` test belongs to H0.

This proves fixed-tuple feasibility for **all** F, including core/long superpositions. It does not choose a functorial L for different tuples. A common phase and common notation for Q_i do not by themselves prove that additional requirement.

## 3. A direct positive formula, and its exact overlap defect

This independent construction is also useful because the failure of a possible marginal claim can be seen explicitly.

Set `q=1/4`, and split each local `L²(0,R)` into short `t<=q` and long `t>q`. Let P denote `|1_(0,R)><1_(0,R)|`. Define

```
b1=(R-q)/(p-q),
b0=(1-p*b1)/(1-p),
B_i(u)=I_short direct_sum b_(chi_i(u)) I_long,
A_i(u)=chi_i(u) P/p.
```

Both `b1>1` and `0<b0<1`. Positivity of b0 follows from

```
1-R-(c-1)q > 0,
```

which holds for `R<1/2`, `c<3`, `q=1/4`. When chi_i=1, the rank-one domination criterion gives

```
A_i <= B_i  <=>  [q+(R-q)/b1]/p <= 1,
```

with equality for the stated b1. Thus `A_i>=0` and `B_i-A_i>=0`.

Define exact-pattern effects by compression to H:

```
E_D = C_R E_u [ tensor_(i in D) A_i(u)
                 tensor_(i notin D) (B_i(u)-A_i(u)) ] C_R.       (8)
```

Every integrand is positive and forbidden patterns vanish. Normalization is not incorrectly inferred from `B_i=I`: those operators are NOT identities. Instead, `R<2q` means that at most one coordinate is long. The B_i are block diagonal with respect to that decomposition, and `E b_(chi_i)=1`. Therefore

```
C_R E_u tensor_i B_i(u) C_R = I_H.                       (9)
```

On the part where all other coordinates are short, the one-prime effect is exactly the full i-integrator. If another coordinate j is long, it is a positive scalar multiple of that integrator. These blocks do not mix. Since `s<q`, T_i is supported entirely in the first block, and (8) dominates T_i. In particular, the short-i/long-i cross terms required by T_i are present, not deleted.

On ordinary total support at most q, all B_i compress to I, and (8) has precisely the original stripe moments. Thus it also meets the ordinary pair/r bounds.

### Failure of the usual tensor marginal identity

For a long spectator j and a short measured coordinate i, the scalar multiplying J_i is

```
k_ij = E[chi_i b_(chi_j)]/p.
```

If i,j form a forbidden edge, `chi_i chi_j=0`, so `k_ij=b0`. At

```
p=2/5, R=9/20, q=1/4,
```

we obtain `b1=4/3`, `b0=7/9`. Take a normalized product F with i uniform on `(0,1/100)` and j uniform on `(2/5,43/100)`. Its total support is below `11/25<9/20`. Then

```
<E_i>_(two-site state)= (7/9)(1/100)=7/900,
<E_i>_(ordinary reduced one-site state)=1/100.
```

The difference is exactly `-1/450`.

Thus (8) must **not** be advertised as satisfying

```
sum_(D intersect A=D0) E_B(D)
 = C_B (E_A(D0) tensor I) C_B.                           (10)
```

It has a common tensor-frame dilation and can be placed in a common phase space, but those facts do not repair (10). Nor is (10) asserted here to be a newly available arithmetic identity. The calculation distinguishes an explicit fixed-tuple completion from a genuine specified overlap extension.

## 4. Keeping the entire p-capped stripe core can obstruct gluing

Here is a finite warning stronger than a failure of formula (8). It concerns **additional model choices**, not the honest arithmetic inputs alone.

Suppose one tries to preserve the original stripe moments on all of the p-capped core, requires the usual cylindrical single-site marginals, and requires the single-site effect to dominate P_R. Consider two very close sites with

```
eta=d/a,
alpha=gamma_ij=(1-eta)/p.
```

Let `h>0`, `m=p-h`, and let ell>0 be a long interval length. Use the orthonormal box states

```
f0 = uniform(0,h) tensor uniform(0,h),
f1 = uniform(h,p) tensor uniform(0,h),
f2 = uniform(0,h) tensor uniform(h,p),
z  = uniform(p,p+ell) tensor uniform(0,h).
```

Choose `p+h<R` and `p+ell+h<R`. The first three states lie in the p-capped core, but generally NOT in the ordinary quarter-simplex.

On their three-dimensional span, put

```
v=(h, sqrt(hm), sqrt(hm)).
```

The pair effect X has core block `alpha v v*`. The one-prime core matrices A_i,A_j are their usual integrator matrices. Let

```
w_i=A_i^+ v,          w_j=A_j^+ v
```

where + is the inverse on the range. Direct calculation gives

```
<w_i,v>=<w_j,v>=p,
<w_i,(A_i-X)w_i>=<w_j,(A_j-X)w_j>=p eta.
```

The cylindrical single-site assumptions force

```
<w_i,E_i z>=sqrt(h ell),
<w_j,E_j z>=0,
<z,E_j z>=h,
<z,E_i z><=1.
```

The first equality uses positivity of `e_i-P_R`: since it compresses to zero on `(0,p)`, its mixed short/long block is zero. Positivity of X forces its core-to-z column to be `v k` for a scalar k. Applying Cauchy–Schwarz to `E_i-X` and `E_j-X` therefore yields the necessary inequality

```
sqrt(h ell) <= sqrt(p eta) (1+sqrt(h)),
or   h ell <= p eta (1+sqrt(h))².                        (11)
```

For the entirely rational choice

```
p=2/5, R=9/20, h=1/100, ell=3/100, eta=1/10000,
```

(11) would read

```
3/10000 <= 121/2500000,
```

which is false. All relevant supports are strictly below R.

This does **not** separate the requested honest data: it used stripe identities on extra, nonordinary p-capped tests, plus a stipulated cylindrical marginal relation. It does show why merely saying “extend the old capped-core dilation globally” needs a real compatibility proof. The fixed-tuple theorem in Section 2 does not supply one.

## 5. A genuinely cylindrical two-site completion

The following alternative avoids both the frame normalization defect and the extra p-capped identities. It preserves the stripe data only where required on ordinary support.

Put `q=z=1/4`, and on `h=L²(0,R)` define

```
L = multiplication by 1_(t>q),
e = P_R + z L,
w(t) = 1                              (0<=t<=q),
       (R-t)/(z+R-t)                  (q<t<=R),
P_w = |w><w|.
```

Thus `e>=P_R`, while e compresses to P_R on ordinary support. This is a **choice of stronger model effect**, not a claim that arithmetic supplies a full-J identity on large support.

For two sites, with H the R-triangle, let

```
A_i=C_H(e tensor I)C_H,
A_j=C_H(I tensor e)C_H,
X_ij=gamma_ij C_H(P_w tensor P_w)C_H.                    (12)
```

Use the four exact-pattern effects

```
X_ij,     A_i-X_ij,     A_j-X_ij,     I-A_i-A_j+X_ij.
```

They are positive for every pair in the target range.

### 5.1 The edge/empty-cell inequality

Weighted Cauchy–Schwarz on each integration fibre gives

```
J_i(F)+J_j(F) <= 2R log(2) ||F||².
```

For example, the i-fibre weight is `R-t_j+t_i`, whose reciprocal integrates to log(2); the two weights sum to 2R. Also `L_i+L_j<=I` on the triangle because `R<2q`. Consequently

```
A_i+A_j <= [2R log(2)+q] I
          < [log(2)+1/4] I < I.                         (13)
```

This proves the empty-cell inequality and handles a forbidden pair, for which X_ij=0.

### 5.2 The two nonprime/prime cells

Let `v(t_i,t_j)=w(t_i)w(t_j)` on the triangle. Since there is at most one long coordinate, v equals 1 on the short core and equals w of the long coordinate on either arm.

A direct inverse quadratic-form computation gives

```
<v,A_i^+ v> = <v,A_j^+ v>
 = q + integral_q^R [w(t)² + (R-t)/z * (w(t)-1)²] dt
 = K(R),

K(R)=R-z log(1+(R-q)/z)=R-(1/4)log(4R).                 (14)
```

Here + denotes the inverse quadratic form on the support of A_i or A_j; its finite value verifies membership in the range of the corresponding positive square root, as required for rank-one domination. The chosen w is the pointwise minimizer of the integrand. The rank-one domination criterion now shows `X_ij<=A_i,A_j`, since

```
gamma_ij K(R) <= c K(R) < 3 K(1/2)
 = 3/2-(3/4)log(2) < 1.                                (15)
```

The strict final inequality follows from `log(2)>2/3`. At the endpoint the bound is approximately `0.980139614580041`.

All pair effects use the SAME e and the same w. Their marginals are genuinely cylindrical. Their ordinary pair moment is `gamma_ij J_ij`, hence below the required 3.99 upper form on its actual tiny-support domain. Single-site and pair positivity, including all cross terms, are therefore solved for this alternative.

## 6. A specific remaining finite operator inequality

Here is an explicit higher-pattern candidate whose only missing property is positivity of certain cells.

First,

```
||w||² = R+q-q²/R-2q log(R/q)
       < K(R) < 1/3 < p.
```

Thus the original common-phase stripe construction with local prime effect `chi_i P_w/p` is a genuine POVM on the FULL tensor product `L²(0,R)^A`. Call its exact effects N_A(D), and set

```
Delta_i = (e-P_w)_i tensor I_(other coordinates).
```

Define, after compression by C_A to the R-simplex,

```
E_A(D) = C_A N_A(D) C_A,                         |D|>=2,
E_A({i}) = C_A [N_A({i})+Delta_i] C_A,
E_A(empty) = C_A [N_A(empty)-sum_i Delta_i] C_A.           (16)
```

These formulas already have the following exact algebraic properties:

* normalization;
* zero forbidden patterns;
* all-prime moment `C_A e_i C_A` for one site, hence domination of the actual T_i;
* all-prime moment `gamma(S) C_A (P_w)_S C_A` for `|S|>=2`;
* ordinary one-prime identities and all the indicated ordinary pair/r uppers;
* literal tensor marginal identities before compression, and (10) afterward.

For the last point, when a coordinate is forgotten, its singleton correction cancels its contribution to the empty correction. Equivalently, every all-prime moment is a fixed cylindrical operator depending only on S.

All cells of size at least two are positive already. The exact remaining inequalities are

```
C_A [N_A(empty)-sum_i Delta_i] C_A >= 0,                  (17a)
C_A [N_A({i})+Delta_i] C_A >= 0       for i in A.          (17b)
```

Neither positivity of the N_A(D) nor separate two-site checks imply (17). In particular `e-P_w` is NOT positive: its short-short block is zero, but its short-long block is nonzero. One cannot paste these correction terms by scalar probability arguments.

### A specified finite case still not proved on its full Hilbert space

Take

```
a=1, b=3/2, R=9/20, s=1/20,
A=(0, 7/5, 14/5, 21/5, 63/20, 21/10, 21/20).
```

In the displayed order this is an induced C7. Its forbidden edges are successive vertices and {7,1}. There are 29 independent patterns. For this tuple the remaining test is exactly the eight inequalities (17): one empty cell and seven singleton cells, on `L²(Delta_7(9/20))`.

There is no unspecified phase integral in this finite test. The active stripe sets and their normalized phase masses are:

| Active set (one-based labels) | Mass |
|---|---:|
| {1,3} | 1/50 |
| {2,4} | 1/50 |
| {3,5} | 1/50 |
| {1,3,5} | 7/50 |
| {1,6} | 1/25 |
| {1,3,6} | 3/25 |
| {4,6} | 1/25 |
| {1,4,6} | 2/25 |
| {2,4,6} | 3/25 |
| {2,7} | 1/50 |
| {2,4,7} | 7/50 |
| {5,7} | 1/25 |
| {2,5,7} | 1/10 |
| {3,5,7} | 1/10 |

For example N_A(empty) is the sum, with precisely these weights, of `tensor_(i active)(I-cP_w)_i`, with identity on inactive coordinates. N_A({i}) uses `c(P_w)_i` and the nonprime factors at other active sites, and only those rows containing i. This fully specifies (17) without unknown higher moments.

A proof of (17) for this C7 would settle this particular finite all-F cylindrical test. It would NOT, by itself, prove the inequalities for all tuples. A negative vector would refute the candidate (16), not the honest input system. More general moments than those in (16) remain allowed by the arithmetic inputs.

## 7. Reproducible finite checks

Run

```
python3 Submission/check_epsilon_band_continuation.py
```

The script uses exact rational phase masses and exact box volumes for the BV truncation, and floating-point matrix eigenvalues for compressed positivity checks. It does not read or use the contents of Spec.lean, only its checksum.

For C7 it uses 15 orthonormal box states. With `h=1/1000`, the three local intervals are

```
short:  (0,1/1000),
medium: (1/1000,61/250),
long:   (2/5,43/100).
```

The states are the all-short product, seven products with one medium coordinate, and seven with one long coordinate. Every box lies in the actual R-simplex. The first eight lie in the ordinary quarter-simplex; the long boxes have total at most `109/250=0.436<0.45`.

Observed results:

```
phase patterns / independent patterns          14 / 29
analytic fixed-tuple Gram margin                19/40
7-dimensional compressed Gram minimum           0.5516287834010523
frame normalization error                      4.44e-16
minimum of all 128 frame exact-cell eigenvalues -2.82e-18
minimum eigenvalue of frame E_i-T_i             -4.18e-17
exact frame marginal discrepancy               -1/450

K(9/20)                                        0.30305333377447025
c K(9/20)                                      0.7576333344361756
||w||²                                         0.2672177786600516
pair edge bound                                0.8738324625039507
candidate (16) minimum on all 128 cells          -1.52e-18
candidate empty-cell minimum                    0.6422118943717369
candidate singleton minimum                    -1.52e-18
all-order ordinary moment maximum error         2.22e-16
complex entangled frame probability sum         1.0000000000000002
candidate tensor marginal identity error        2.22e-16
```

The tiny negative eigenvalues are numerical roundoff, not certified analytic lower bounds. The Naimark theorem and the two-site theorem have analytic proofs above; **the full-space 7-cycle inequalities (17) have not been certified by this finite computation**.

The script also verifies (11)'s exact rational failure and the unchanged Spec.lean checksum.

## 8. Arithmetic conclusion and what remains

The fixed-tuple theorem rules out a separation using only the displayed forms in one tuple. It is an information-compatibility theorem, not an integer or prime realization. The explicit overlap defects are failures of proposed abstract extensions, not violations of Bombieri–Vinogradov.

What remains is a positive completion with the required, explicitly justified overlap maps for all finite tuples, or an honest separation involving additional legitimate overlap/arithmetic information. The concrete sufficient candidate (16) reduces one version of that task to (17); its single-site and two-site inequalities are proved, and its stated C7 compression passes, but its higher all-F inequalities are open in this analysis.

No forbidden-all-pair-differences conclusion has been derived, and certainly no consecutive-gap conclusion. Missing consecutive gaps is weaker than forbidding every pair difference in the band. A future independent-set separation would still need a separate geometric/arithmetic argument ensuring consecutivity before it could bear on Erdős #5.
