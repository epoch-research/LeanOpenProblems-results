# Pinned projections: an extremal-stable spectral obstruction, not a closing inequality

## Status

**No proof of WR, of `E D^2 >= c n^5`, or of the sharp distinct-distances theorem was obtained. The logarithmic-moment proposal is neither proved nor refuted. No Lean file was changed.**

There is, however, a rigorous obstruction specific to the new, genuinely positive pinned operators. It is not the supplied isolated-origin example and does not disappear upon hereditary ratio selection:

> Every nontrivial finite rational planar configuration has a nonconstant common fixed vector for all its full pinned projections. Consequently, for actual hereditary ratio-maximizing subsets of growing square grids, `K=n/D -> infinity` while
> 
> `||(M - n Pi_1)|| = n`,
> 
> where `Pi_1` projects onto the constant functions.

Thus even on the actual extremal class there is **no** bound `M-n Pi_1 <= C D I`, no uniform spectral gap below `n` on the mean-zero space, and no pairwise contraction of the centered pinned projections. These are obstructions to specific spectral closing mechanisms, not a disproof of all possible uses of the operators.

Two further facts sharpen the diagnosis:

* For **every** real planar set, the proposed coordinate identity forces `lambda_2(M) >= n/3`. It supplies a large eigenvalue, not mean-zero spectral dispersion.
* On even-sided square grids the common fixed vector is orthogonal to `1, x, y, |z|^2`. Projecting away exactly the advertised coordinate modes still leaves operator norm `n` in the low-distance regime. This latter coordinate-orthogonality assertion is for the grids themselves; it is not asserted to survive arbitrary extremal selection.

The proofs below retain actual pins, full fibers including radius zero, circle intersection, and the actual Euclidean reflection axes. No abstract colored model or numerical search is used.

## 1. Conventions and the exact reflection decomposition

Let `P` have `n>=2` distinct points, let `S` be its positive squared-distance palette, and put `D=|S|`. For a pin `p`, include the zero fiber:

```
F_{p,s} = {a in P : |a-p|^2=s},
k_{p,s} = |F_{p,s}|,
k_p(a) = k_{p,|a-p|^2}.
```

Write `d_p` for the number of positive nonempty fibers. For positive `s`, the ordered global multiplicity is `r_s=sum_p k_{p,s}` (empty fibers contribute zero), and `E=sum_s r_s^2`. On the real Hilbert space of functions on `P`, with counting-measure inner product,

```
A_p = sum_{s:F_{p,s} nonempty} (1/k_{p,s}) 1_{F_{p,s}} 1_{F_{p,s}}^T.
```

These are nonnegative symmetric orthogonal projections. In particular,

```
M = sum_p A_p,
0 <= M <= n I,       M 1 = n 1,
T := tr M = sum_p(d_p+1) <= n(D+1).
```

For each perpendicular bisector axis `l`, put `m_l=|P intersect l|`, and let `E_l` be the ordered pairs `(a,b)` with `a!=b` and `b` the reflection of `a` in `l`. Thus `w_l=|E_l|`. For such a pair define

```
g_l(a) = sum_{p in P intersect l} 1/k_p(a).
```

The reflected pair has equal distance from every such pin, so `g_l(a)=g_l(b)`. Moreover, **every** actual pin equidistant from `a,b` lies on this unique axis. Therefore

```
M_ab = g_l(a)                    (a!=b, l=bisector(a,b)).
```

Let

```
L_l = sum_{unordered {a,b}, bisector(a,b)=l}
           g_l(a) (e_a-e_b)(e_a-e_b)^T.
```

Then, exactly,

```
L := n I-M = sum_l L_l,
L_l >= 0,
D h_l = tr L_l = sum_{(a,b) in E_l} g_l(a),
D B = tr L = n(n-1)-sum_p d_p.
```

The diagonal equality in the first formula follows from the zero row sums of both sides; the off-diagonal equality was proved above. This recovers precisely the weights `1/(D k_{p,s})` on ordered witnesses in the two WR files, without removing singleton fibers or renormalizing on an axis.

There is also an exact rank calculation. If `m_l>0`, all `g_l(a)>0`; reflection pairs are disjoint, and each pair contributes the positive block

```
g_l(a) [ 1 -1 ; -1 1 ].
```

Hence

```
rank L_l = w_l/2,
||L_l|| = 2 max_{(a,b) in E_l} g_l(a) <= m_l.
```

The last inequality uses `k_p(a)>=2` on a nonfixed reflected pair. **The rank is not capped by `O(m_l^2)`.** The actual modified-grid axes in Section 3 of `wr_two_center_cap_obstruction.md` have `m_l -> infinity` and `w_l/m_l^2 -> infinity`. They therefore also disprove such a rank cap for these positive reflection blocks. Their normalized trace satisfies `h_l/m_l -> 1`, as already proved there.

This is not a contradiction to WR: a rank cap or a vanishing per-axis trace discount is stronger than the requested global estimate. It does locate precisely where positivity fails to insert the missing `min(w_l,m_l(m_l-1))` automatically.

## 2. What circle intersection really gives at the second moment

Define

```
delta_a = M_aa = sum_p 1/k_p(a),
eta_a = sum_p 1/k_p(a)^2.
```

For distinct pins `p,q`, let

```
c_{s,t} = |F_{p,s} intersect F_{q,t}|.
```

Two positive-radius circles with distinct centers meet in at most two points; zero-radius fibers are singletons. Thus `c_{s,t} in {0,1,2}` and

```
tr(A_p A_q) = sum_{s,t} c_{s,t}^2/(k_{p,s} k_{q,t}).
```

Since `c <= c^2 <= 2c` for these integers,

```
sum_a 1/(k_p(a) k_q(a))
    <= tr(A_p A_q)
    <= 2 sum_a 1/(k_p(a) k_q(a)).
```

Including the `p=q` terms, which equal `tr A_p`, gives the unconditional two-sided estimate

```
T + sum_a (delta_a^2-eta_a)
    <= tr M^2
    <= T + 2 sum_a (delta_a^2-eta_a).               (2.1)
```

This uses genuine circle intersection, not just PSD. But its upper bound is in terms of squared diagonal loads. It does **not** prove a uniform bound on those loads. In particular, the supplied origin-plus-parity-square example has `delta_0=n`, so replacing `delta_a` by `O(D)` is false before selection. Nothing in (2.1) proves that replacement after selection, either.

The same second moment also has the exact reflection expression

```
tr M^2 = sum_a delta_a^2
           + sum_l sum_{(a,b) in E_l} g_l(a)^2.     (2.2)
```

It is the squared actual edge weight, not the capped quantity in WR. Equations (2.1)--(2.2) are useful identities/estimates, not an amplification theorem.

## 3. The coordinate relation forces a macroscopic nonconstant eigenvalue

### Proposition 3.1

For every finite real planar `P`, `n>=2`,

```
lambda_2(M) >= n/3.
```

Here eigenvalues are in decreasing order with multiplicity, so one copy of the eigenvalue `n` belongs to the constants.

### Proof

Let `X(a)=a_x`, `Y(a)=a_y`, and `Q(a)=|a|^2`. Subtract their means to obtain `X_0,Y_0,Q_0`, and set

```
V_0 = span{X_0,Y_0,Q_0} subset 1^perp,
r = dim V_0 <= 3.
```

For every actual pin `p`,

```
f_p = Q_0 - 2 p_x X_0 - 2 p_y Y_0
```

is the centered squared-distance function about `p`. It is nonzero: the uncentered function is zero at `p` and positive somewhere else. It is constant on each full fiber, so `A_p f_p=f_p`.

Let `P_0` be the orthogonal projection onto `V_0`. The compression `P_0 A_p P_0` is PSD and has a unit vector with eigenvalue one, namely `f_p/||f_p||`. Thus

```
tr(P_0 A_p P_0) >= 1,
tr(P_0 M P_0) >= n.
```

The largest Rayleigh quotient on `V_0` is at least `n/r >= n/3`. Since `M` preserves `1^perp`, the variational principle proves the assertion. QED.

Consequently, in any family with `K=n/D -> infinity`,

```
||M - n Pi_1||/D >= K/3 -> infinity.               (3.1)
```

This is an obstruction even without lattice arithmetic. The coordinate identity cannot be used to justify an `O(D)` centered operator norm: it contradicts that norm bound.

## 4. Rational Euclidean geometry gives a common fixed vector

### Proposition 4.1

For every nontrivial finite `P subset Q^2`, there is a partition

```
P = C_0 disjoint_union C_1,       C_0,C_1 nonempty,
```

such that every full equal-distance fiber about every actual pin is contained entirely in one class. Hence

```
A_p 1_{C_i}=1_{C_i}     for all p and i,
||M-n Pi_1||=n.                                  (4.1)
```

The assertion also holds for any configuration similar to a rational one.

### Proof: normalization and parity

Translate one point to the origin and clear denominators. Divide every coordinate by the largest common power of two, so the resulting set is integral, contains the origin, and contains a point with an odd coordinate. These operations are similarities and do not change any distance-equality fiber.

If some point has odd squared norm, use the two classes of squared-norm parity. Otherwise all points have even squared norm, so every point has coordinates of the same parity. Apply the further similarity

```
(x,y) -> ((x+y)/2, (y-x)/2).
```

It maps this set to integer points. A point with an odd coordinate had both coordinates odd, so its new squared norm `(x^2+y^2)/2` is odd. The origin still has even squared norm. Thus in either case we have integer coordinates with both norm-parity classes nonempty.

For any pin and endpoints in these coordinates,

```
|p-a|^2=|p-b|^2
    => |a|^2-|b|^2 = 2 p dot (a-b)
    => |a|^2 = |b|^2 (mod 2).
```

So a fiber cannot cross the two classes, including when it is the singleton `{p}`. Their indicators are fixed by every averaging projection. The vector

```
v = |C_1| 1_{C_0} - |C_0| 1_{C_1}
```

is nonzero and mean zero, and satisfies `A_p v=v`, hence `Mv=nv`. Since `0<=M<=nI`, (4.1) follows. QED.

This also proves, for all pins `p,q`,

```
||(A_p-Pi_1)(A_q-Pi_1)|| = 1.                    (4.2)
```

Indeed each factor is an orthogonal projection on the mean-zero part of its range, and both fix `v`. Thus circle intersections of size at most two do not imply a strict angle between the centered ranges.

### 4.2 A genuine hereditary-extremal counterexample to a spectral-gap repair

Let `G_L={0,...,L-1}^2`. Choose `Q_L` maximizing `|Q|/D(Q)` over all nontrivial subsets of `G_L`; among ties, choose one of minimum cardinality. These are actual finite Euclidean sets and satisfy full hereditary ratio extremality.

We use only the already supplied grid fact `K(G_L)->infinity` (indeed `K(G_L) >> sqrt(log L)`); no new arithmetic asymptotic is needed. Then

```
K(Q_L) >= K(G_L) -> infinity,
|Q_L| -> infinity,
D(Q_L)/|Q_L| -> 0.
```

Every `Q_L` is rational, regardless of its size, density, or shape. Proposition 4.1 therefore applies **directly to its own full pinned projections**:

```
||M_{Q_L} - |Q_L| Pi_1|| / D(Q_L)
      = K(Q_L) -> infinity.                      (4.3)
```

This proves failure of the centered `O(D)` bound and of any uniform mean-zero spectral gap on the genuine hereditary-extremal class. No transfer of an operator estimate from `G_L` to `Q_L` is being assumed.

The tie-breaking also shows that every proper nontrivial subset of `Q_L` has strictly smaller `K`. In particular, replacing `Q_L` by a proper nontrivial common-invariant component cannot preserve its maximizing ratio. This is a concrete obstruction to repairing irreducibility by simply selecting one such component.

In fact, Proposition 4.1 applies again after **any** nontrivial rational subset selection and recomputation of the projections. There is no nontrivial rational actual-pin configuration whose common fixed space consists only of constants. An irreducibility hypothesis of that kind excludes all these configurations, not merely the initial square.

There is a further operator distinction. If `C` is a common-invariant component for a set `P`, then

```
M_P restricted_to C = M_C + sum_{p in P\C} A_{p,C}.
```

Here `A_{p,C}` averages the distance fibers on `C` about the **external** pin `p`. All are positive projections, but they are not actual-pin summands of `M_C`. The block of the old operator has row sum `|P|`; the new actual-pin sum has row sum `|C|`. Even an invariant-component selection does not identify these two operators.

## 5. Removing the coordinate modes does not fix the grid operator

Let `L` be even, `P=G_L`, and set

```
u(x,y)=(-1)^(x+y),
V = span{1,X,Y,Q}.
```

The parity calculation gives `A_p u=u` for every pin. On the other hand, with `S_0=sum_{i=0}^{L-1}(-1)^i=0`,

```
<u,1> = S_0^2 = 0,
<u,X> = (sum_i (-1)^i i) S_0 = 0,
<u,Y> = 0,
<u,Q> = (sum_i (-1)^i i^2) S_0
          + S_0 (sum_i (-1)^i i^2) = 0.
```

Thus `u` is orthogonal to every function `|z|^2-2p dot z`, as well as to the constants. If `Pi_V` is the orthogonal projection onto `V`, then

```
||(I-Pi_V) M (I-Pi_V)|| = n.                      (5.1)
```

The lower bound follows by applying the compression to `u`; the upper bound follows from `M<=nI`. Since these grids have `D=o(n)`, no `O(D)` bound holds even for this coordinate-cleaned compression.

Again, this is a theorem for the even grids, not a claim that the same coordinate orthogonality holds for all their extremal subsets. The extremal-stable statement is (4.3).

## 6. Exact boundary of the obstruction and the remaining task

The following potential shortcuts are now rigorously excluded:

1. Centering each projection by the constants and using a strict pairwise contraction from two-circle intersection: false by (4.2), even for every pair of actual pins in the rational configurations.
2. Bounding `M-n Pi_1` by `O(D)` after hereditary ratio selection: false by (4.3).
3. Removing just `1,x,y,|z|^2` and claiming such a norm bound on low-distance sets: false by (5.1).
4. Inserting the WR cap as a rank bound for the positive reflection blocks: false because their exact ranks are `w_l/2`, including on the existing overfull-axis family.

These are not counterexamples to

```
tr(M^k) <= n (C sqrt(k) D)^k,       k comparable to log n.
```

That estimate allows eigenvalues of size `n` when `sqrt(k)D` is of order `n`. In particular, an additional eigenvalue `n` only gives `tr M^k >= 2 n^k`; it does not contradict the proposed right-hand side with an unspecified universal constant. No claim is made that removing the **entire** common fixed space yields or fails the desired moment estimate; such a removal would require a separate argument and accounting for the removed modes.

Nor do the results prove that the diagonal bound `max_a M_aa=O(D)` fails on hereditary maximizers. The supplied outlier refutes it without selection; (4.3) refutes a different, spectral bound **with** selection. Conflating these statements would be an error.

What is still missing is a genuinely global estimate on these full weighted fibers that supplies either

```
B^2 <= C [ n^2 + sum_l m_l min(w_l,m_l(m_l-1)) ],
```

or `E D^2 >= c n^5`, or the stated logarithmic moment. Positivity, the exact second-moment circle bound, and the coordinate fixed-vector relation above do not supply it. I have not established a decisive obstruction to *every possible* pinned-projection proof; the decisive obstructions here concern the specified gap, contraction, coordinate-removal, and rank-cap mechanisms.

## Verification and file integrity

The arguments above are deductive. In particular, the extremal obstruction is proved uniformly for **all** rational subsets, rather than tested on a purported numerical maximizer. The reflection weights were checked against the ordered-witness conventions in both WR files; the singleton radius contributes one to each `tr A_p` and is retained throughout.

An exact rational-arithmetic audit on one fixed `4 by 4` square also checked the projection identities, (2.1), (2.2), the reflection decomposition, and the parity/coordinate fixed-vector identities. It returned `n=16`, `D=9`, `tr M=136`, `D B=120`, and `tr M^2=1312`; the two bounds in (2.1) were `10856/9` and `20488/9`. This was a formula audit, not a search or asymptotic evidence. The proofs, not that finite audit, establish the results.

`Submission/Spec.lean` was left unchanged. Its SHA-256 remains

```
c2fbaabe5ad8088f856ca97625747c7a01754f3c149dd6a493454e776de290db
```

## Parent audit: status of the logarithmic moment reformulation

The parity normalization, positive reflection blocks, second-moment estimate,
and coordinate-compression argument above were independently checked. They do
not prove the missing upper bound.

There is also an exact scope check on the proposed high moment. Put
`k=ceil(log n)` for `n>=3`, and let `D` be the positive distance count. Since
`M` is positive semidefinite, has eigenvalue `n`, and all its eigenvalues are at
most `n`,

```
n^k <= tr(M^k) <= n^(k+1).
```

Consequently, a uniform estimate

```
tr(M^k) <= n (C sqrt(k) D)^k
```

implies

```
n <= C n^(1/k) sqrt(k) D <= e sqrt(2) C sqrt(log n) D.
```

Conversely, the conjectural uniform bound `n <= A sqrt(log n) D` immediately
implies that moment estimate with `C=A`, since `k>=log n` and
`tr(M^k)<=n^(k+1)`. Thus, at this logarithmic exponent, the moment formulation is
equivalent up to absolute constants to the original arbitrary-set conjecture.
It is not an additional proven estimate. A useful projection approach must
supply a nontrivial upper bound; the presently verified identities do not do so.

No theorem in `Spec.lean` has been filled in, and none of these obstructions is
a disproof of its original statement.
