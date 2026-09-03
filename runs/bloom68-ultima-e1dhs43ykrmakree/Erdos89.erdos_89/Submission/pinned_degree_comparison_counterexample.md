# A low-distance, diffuse-pin counterexample to E >= c n I

## Status

**The comparison `E >= c n I` is false in `D=o(n)`, even when every pin contributes within absolute constant factors of the average isosceles count.** This is an actual planar integer-coordinate construction, not a color-table relaxation. Removing a sparse exceptional set of pins cannot repair the comparison.

The separate amplification

\[
 (I+n^2)D^2\ge c n^4
\]

is **not proved or disproved here**. Neither the sharp distinct-distance conjecture nor the global target `ED^2 >= c n^5` is settled. The counterexample invalidates the proposed comparison, including its natural diffuse-pin restriction; it does not rule out a substantially different, color-sensitive restricted comparison.

No Lean files are changed.

## 1. Main theorem and parameters

All distances below are positive squared distances. Pairs and the two equal-radius neighbors of a pin are ordered:

\[
 k_{p,s}=|\{q\in P:|p-q|^2=s\}|,\quad
 r_s=\sum_p k_{p,s},\quad E=\sum_s r_s^2,
\]
\[
 I_p=\sum_s k_{p,s}(k_{p,s}-1),\qquad I=\sum_p I_p.
\]

There are absolute constants `c,C>0` and planar integer sets `P_m`, for every sufficiently large integer `m`, with `n=|P_m|`, such that

\[
 \boxed{D(P_m)\le C\frac{n(\log\log n)^{15}}{\sqrt{\log n}}=o(n),}
 \tag{1.1}
\]
\[
 \boxed{I(P_m)\asymp\frac{n^2\log n}{\log\log n},\qquad
 E(P_m)\asymp\frac{n^3\log n}{(\log\log n)^2}.}
 \tag{1.2}
\]

Moreover, **uniformly for every pin**,

\[
 \boxed{c\frac{I}{n}\le I_p\le C\frac{I}{n}.} \tag{1.3}
\]

Consequently

\[
 \boxed{\frac{E}{nI}\asymp\frac1{\log\log n}\longrightarrow0.} \tag{1.4}
\]

In particular, `D <= (n-1)/2` holds eventually, and the comparison fails in the explicitly stated sublinear-support regime. Equation (1.3) rules out an explanation by a sparse set of exceptional pins.

### Construction

Put

\[
 T=m^5,\qquad M=2^{2^m}.
\]

Choose distinct primes

\[
 T\le p_1,\ldots,p_m\le2T,\qquad p_i\equiv3\pmod4.
\]

These exist for every sufficiently large `m`: the prime number theorem in the fixed progression `3 mod 4` gives asymptotically `T/(2 log T)` such primes in `[T,2T]`, and this quantity divided by `m` tends to infinity.

Index the blocks by `i=0,...,m-1`, relabeling the primes accordingly, and set

\[
 B_i=4m^2 i+i^2,\qquad b_i=(32TM B_i,0),
\]
\[
 P_i=b_i+p_i\{0,\ldots,M-1\}^2,\qquad P_m=\bigcup_{i=0}^{m-1}P_i.
 \tag{1.5}
\]

The blocks are disjoint, so `n=mM^2`. The estimates proved below, before substituting `M`, are

\[
 \begin{split}
 D&\ll m^{15}\frac{n}{\sqrt{\log M}},\\
 I_p&\asymp M^2\log M\quad\text{for every }p\in P_m,\\
 I&\asymp mM^4\log M,\\
 E&\asymp mM^6\log M.
 \end{split}                                                   \tag{1.6}
\]

All implicit constants are absolute, independent of `m`, `M`, and the selected primes. Since `log n ~ 2 log M` and `log log n = m log 2 + O(1)`, (1.1)--(1.4) follow.

Only two standard arithmetic facts are used: the prime count just specified, and the Landau--Ramanujan upper bound for the number of sums of two squares. The needed second-moment bound for representations is elementary; a proof is supplied next.

## 2. Elementary lattice-counting lemmas

Write

\[
 r_2(s)=|\{z\in\mathbb Z^2:|z|^2=s\}|,\qquad
 H(X)=\sum_{1\le s\le X}r_2(s)^2.
\]

### Lemma 2.1: representation second moment

There are absolute positive constants such that, for all sufficiently large `X`,

\[
 cX\log X\le H(X)\le CX\log X.                         \tag{2.1}
\]

Also `sum_(s<=X) r_2(s) <= 9X` for `X>=1`.

**Proof.** For the upper bound count integer vectors `u,v` with `|u|=|v|<=sqrt X`. Put `a=u+v`, `b=u-v`; then `a dot b=0`, and both norms are at most `2 sqrt X`. Cases with `a=0` or `b=0` contribute `O(X)`. Otherwise, for a primitive integer vector `w`, write

\[
 a=g w,\qquad b=h w^\perp,
\]

with nonzero integer multipliers. Their number for fixed `w` is `O(X/|w|^2)`. Summing over `0<|w|<=2 sqrt X`, and even dropping primitivity, gives `O(X log X)` by dyadic annuli. Dropping the parity requirement on `a,b` is harmless for this upper bound.

For the lower bound, choose primitive `w=(a,b)` with `a,b>0`, and positive integers

\[
 1\le g,h\le \left\lfloor\frac{\sqrt X}{2|w|}\right\rfloor.
\]

Then

\[
 u=g w+h w^\perp,\qquad v=g w-h w^\perp
\]

are integer vectors of equal positive squared norm at most `X/2`. The triples `(w,g,h)` are recovered from `(u,v)`, so this is injective. For `|w|<=sqrt X/4`, they give at least `X/(16|w|^2)` pairs.

There are at least `cR^2` primitive positive vectors with `R/2 < max(a,b) <= R` for every dyadic integer `R`. Indeed, the number of noncoprime pairs in `[1,R]^2` is at most

\[
 \sum_{p\text{ prime}}\lfloor R/p\rfloor^2
 \le R^2\sum_{k=2}^\infty k^{-2}
 =R^2(\pi^2/6-1).
\]

After also subtracting the inner square, the remaining number is at least `(7/4-pi^2/6)R^2>0`. Thus the sum of `1/|w|^2` over the permitted primitive vectors is at least `c log X`. This proves the lower bound. Finally, a disk of radius `sqrt X` is contained in an integer square with at most `(2 sqrt X+1)^2<=9X` points. QED.

### Lemma 2.2: every pin of a square grid is rich

For `G_M={0,...,M-1}^2`, every `p in G_M` satisfies

\[
 cM^2\log M\le I_p(G_M)\le CM^2\log M,                 \tag{2.2}
\]

for all sufficiently large `M`. Its ordered distance energy satisfies

\[
 cM^6\log M\le E(G_M)\le CM^6\log M.                   \tag{2.3}
\]

**Proof.** For every pin choose a horizontal and a vertical direction with at least `a=floor((M-1)/2)` available grid steps. The corresponding closed quadrant contains at least `r_2(s)/4` neighbors at each squared radius `s<=a^2`. Thus

\[
 I_p\ge\frac1{16}H(a^2)-\frac14\sum_{s\le a^2}r_2(s)
 \gg M^2\log M.
\]

The upper bound follows from `k_(p,s)<=r_2(s)` and `s<=2M^2`.

For energy, a difference vector `(x,y)` has multiplicity `(M-|x|)(M-|y|)`, at most `M^2`. When `x^2+y^2<=a^2`, this multiplicity is at least `M^2/4`. Sandwich the corresponding energy between constant multiples of `M^4 H(a^2)` and `M^4 H(2M^2)`, and apply Lemma 2.1. QED.

### Lemma 2.3: a far-away pin sees few grid isosceles pairs

Let `u` be any real point, `c_M=((M-1)/2,(M-1)/2)`, and `d=|u-c_M|>=2M`. The number `J_M(u)` of ordered distinct `q,r in G_M` with `|q-u|=|r-u|` satisfies

\[
 \boxed{J_M(u)\le CM^2\left(1+\frac M d\log(2M)\right).} \tag{2.4}
\]

No rationality of `u` is assumed.

**Proof.** Write `q-r=g v`, with `v` a primitive integer direction and `g` a nonzero integer. For fixed `v`, there are `O(M/|v|)` possible multipliers. For each multiplier the equality of the two distances is the line equation

\[
 2q\mathbin\cdot v=g|v|^2+2u\mathbin\cdot v.
\]

If this line has integer solutions, consecutive ones are separated by `|v|`, because `v` is primitive. Its intersection with `G_M` therefore has `O(M/|v|)` solutions. Here `|v|<=sqrt(2)(M-1)`, so the possible additive `1` is absorbed. The contribution per direction is `O(M^2/|v|^2)`.

The midpoint of the chord lies in the grid square. Consequently its direction `v` is perpendicular to a vector from `u` to that square. Since `d>=2M`, all permissible directions belong to two antipodal angular intervals of total length `O(M/d)`.

For any angular intervals of total length `theta`, the number of integer vectors with norm between `R` and `2R` in those intervals is `O(theta R^2+R+1)`, uniformly in their orientation. This follows by covering the lattice points with unit squares and bounding the area and boundary length of the sectors. Summing `1/|v|^2` over dyadic annuli, with primitivity dropped for an upper bound, gives

\[
 O\left(1+\theta\log(2M)\right).
\]

Substitute `theta=O(M/d)`. QED.

## 3. The separation makes the actual pin counts diffuse

### 3.1 No isosceles pair has endpoints in two different blocks

For a fixed `i`, the numbers `|B_i-B_j|`, including zero for `j=i`, are pairwise distinct integers. Strict monotonicity handles indices on the same side. For `j=i-a`, `k=i+b`, `a,b>=1`, an equality would require

\[
 B_j+B_k-2B_i=(4m^2+2i)(b-a)+a^2+b^2=0.
\]

If `b>=a` the expression is positive. If `b<a`, it is negative, since `a^2+b^2<2m^2<4m^2`. Thus it is never zero.

Every point of `P_i` lies within `3TM` of `b_i`. For `p in P_i`, `q in P_j`, therefore,

\[
 \big||p-q|-32TM|B_i-B_j|\big|<6TM.                    \tag{3.1}
\]

The intervals in (3.1), indexed by `j`, are disjoint, since their centers are separated by at least `32TM`. The same assertion includes the self block, whose distances are smaller than `6TM`. Thus, **for every pin**, equal-distance endpoints must lie in the same block. This is an exact statement about the actual complete fibers.

### 3.2 Uniform upper and lower bounds at every pin

The self block gives `I_p>=cM^2 log M` by similarity and Lemma 2.2.

For `p in P_i`, consider endpoints in `P_j`, `j!=i`, and normalize by that block's spacing. The normalized pin is `u=(p-b_j)/p_j`. Since

\[
 |B_i-B_j|=|i-j|(4m^2+i+j)\ge4m^2|i-j|,
\]

its distance to the normalized grid center is at least

\[
 d\ge50M m^2|i-j|.                                     \tag{3.2}
\]

For example, subtracting the two endpoint-to-block-center errors costs less than `5TM` from the base separation `128TM m^2|i-j|`, and then divide by `p_j<=2T`.

Lemma 2.3 bounds this block's contribution by

\[
 CM^2\left(1+\frac{\log(2M)}{m^2|i-j|}\right).
\]

There are no cross-block endpoint pairs by Section 3.1. Summing these bounds and the self-block bound gives

\[
 I_p\le CM^2\left(\log M+m+
                   \frac{1+\log m}{m^2}\log M\right)
 \le C'M^2\log M,                                      \tag{3.3}
\]

using `log M>=m`, which holds eventually. This proves the uniform assertions about `I_p` and hence `I` in (1.6).

In particular, for every set of pins `H subset P_m`,

\[
 \frac{\sum_{p\in H}I_p}{I}\le C\frac{|H|}{n}.          \tag{3.4}
\]

Thus every `o(n)` set of pins carries `o(I)`, not an exceptional dominant mass. Even discarding any half of the pins leaves at least `c n M^2 log M` isosceles mass, while the same upper bound on `E` below continues to apply.

## 4. Energy: internal color localization and small cross energy

Write `r_s=r_s^in+r_s^out`, according as the endpoints are in the same or in different blocks. Positivity gives

\[
 E\le2E_{in}+2E_{out}.                                  \tag{4.1}
\]

### 4.1 Different grid blocks have almost disjoint internal distance palettes

Let `r_i(s)` be the ordered multiplicity inside `P_i`. It vanishes unless `p_i^2` divides `s`, and

\[
 r_i(s)\le M^2 r_2(s/p_i^2),\qquad s\le2p_i^2M^2.       \tag{4.2}
\]

For an inert prime `p=3 mod 4`,

\[
 r_2(p^2 t)=r_2(t)                                      \tag{4.3}
\]

exactly: `p | x^2+y^2` forces `p | x,y`, and division by `p` is the required bijection of representations.

For distinct blocks, a common positive color must have `s=p_i^2p_j^2 t`, with

\[
 t\le\frac{2M^2}{\max(p_i^2,p_j^2)}\le\frac{2M^2}{T^2}.
\]

Consequently, by (4.2)--(4.3),

\[
 \sum_s r_i(s)r_j(s)
 \le M^4 H(2M^2/T^2)
 \ll \frac{M^6}{T^2}\log M.                            \tag{4.4}
\]

The diagonal block energies are `Theta(M^6 log M)` by Lemma 2.2. Therefore

\[
 c mM^6\log M\le E_{in}
 \le C\left(m+\frac{m^2}{T^2}\right)M^6\log M.          \tag{4.5}
\]

### 4.2 Uniform translation-multiplicity bound between different blocks

Fix a vector `z` and an ordered pair of distinct blocks `i,j`. In each coordinate, the equation for a pair with difference `z` is

\[
 p_i a-p_j b=\text{a fixed integer},\qquad 0\le a,b<M.
\]

Because the two primes are coprime, its solutions form a progression

\[
 a=a_0+p_j t,\qquad b=b_0+p_i t.
\]

Thus there are at most `1+M/max(p_i,p_j)<=1+M/T` choices per coordinate. Since `M>=T`, the two-dimensional multiplicity is at most `4M^2/T^2`. Summing over ordered block pairs gives, for **every** difference vector,

\[
 a_{out}(z)\le4m^2M^2/T^2.                             \tag{4.6}
\]

All squared distances in the construction are at most

\[
 X=(200TMm^3)^2.                                       \tag{4.7}
\]

For instance `max B_i<4m^3`, the horizontal base span is less than `128TMm^3`, and the additional block dimensions are less than `2TM` in each coordinate. Also `log X<=3 log M` eventually.

By (4.6),

\[
 r_s^{out}\le\frac{4m^2M^2}{T^2}r_2(s).
\]

Hence Lemma 2.1 gives

\[
 E_{out}\le\frac{16m^4M^4}{T^4}H(X)
 \ll\frac{m^{10}}{T^2}M^6\log M
 =O(M^6\log M),                                       \tag{4.8}
\]

where the last equality uses `T=m^5`.

Equations (4.1), (4.5), and (4.8) prove `E << mM^6 log M`. Conversely, since all multiplicities are nonnegative, the full energy is at least the sum of the `m` separate block energies. Thus

\[
 \boxed{E\asymp mM^6\log M.}                            \tag{4.9}
\]

This proof controls the actual global energy, including every cross-block distance coincidence; it does not assert that separated blocks have disjoint cross-distance palettes.

## 5. The actual global distance count is sublinear

All points have integer coordinates. The Landau--Ramanujan upper bound is

\[
 |\{1\le s\le X:s=x^2+y^2\text{ for integers }x,y\}|
 \ll X/\sqrt{\log X}.
\]

Using (4.7), `n=mM^2`, and `T=m^5`,

\[
 \frac D n\ll\frac{m^5T^2}{\sqrt{\log M}}
 =\frac{m^{15}}{\sqrt{\log M}}
 \asymp\frac{m^{15}}{2^{m/2}}\longrightarrow0.           \tag{5.1}
\]

This is the correct direction of the estimate: an ambient palette **upper** bound suffices to certify `D=o(n)`. No asymptotic equality for `D` is needed or claimed.

Together with Sections 3--4 this completes the counterexample, including diffuseness and all asymptotic hypotheses.

### Robustness under deleting actual points

The obstruction is also robust under deleting `o(n)` points, not only under omitting their pin contributions. Each point belongs to at most `CM^2 log M` ordered isosceles triples internal to its own block, counting all three roles. The apex bound is Lemma 2.2. For a fixed endpoint, the map to the two equal-norm difference vectors is injective, and bounds its contribution by `H(2M^2)`; count both endpoint roles.

Thus deleting `o(n)` points destroys only `o(nM^2 log M)` of the internal triples. The remaining set `P'` has `n'~n`, still has `D(P')=o(n')`, and satisfies

\[
 I(P')\gg n'M^2\log M,\quad
 \max_p I_p(P')\ll M^2\log M,\quad
 \frac{E(P')}{n'I(P')}=O(1/m)\longrightarrow0.
\]

So both the failure and the bounded maximum-to-average pin ratio survive sparse vertex deletion.

## 6. What the degree matrix and centroid moments actually say

Let

\[
 B_{p,s}=k_{p,s}-r_s/n,\qquad
 \Delta=\sum_{p,s}B_{p,s}^2.
\]

Exactly,

\[
 \boxed{I=E/n-n(n-1)+\Delta,\qquad I+n^2=E/n+\Delta+n.} \tag{6.1}
\]

In the construction,

\[
 I/n^2\asymp\log M/m\longrightarrow\infty,\quad
 \Delta\asymp I,\quad \frac{\Delta}{E/n}\asymp m.
\]

The large defect is **color-specific pin localization**, not a large value of `I_p` on a few pins. Every pin has many internal-grid triples, but their colors depend on that pin's block. This is why a diffuse-pin condition alone cannot turn pin energy into global color energy.

For completeness, center the points at their centroid, put `q_p=|p-centroid|^2` and `V=sum_p q_p`. The exact first-moment identity and its centered form are

\[
 \sum_s s k_{p,s}=nq_p+V,\qquad
 \sum_s s B_{p,s}=n(q_p-V/n).                           \tag{6.2}
\]

Since every row of `B` sums to zero, for `D>=2` and `bar s=D^{-1}sum_s s`, Cauchy--Schwarz yields

\[
 \Delta\ge
 \frac{n^2\sum_p(q_p-V/n)^2}
      {\sum_s(s-\bar s)^2}.                            \tag{6.3}
\]

This is a valid weighted projection bound, not the requested amplification. It must not be reversed to infer small `Delta` from a thin annulus.

Exact `B=0` implies constant `q_p`; hence a centroid circle and `D>=(n-1)/2`. The exact shell statement also remains valid: a positive-radius centroid shell has at most `2D+1` points, by the at-most-two intersections of circles. Neither statement supplies a uniform quantitative stability principle.

### Thin centroid annuli really can have D=o(n)

There is a separate elementary obstruction to replacing the exact circle conclusion by a uniform relative-thickness conclusion. Let

\[
 A_R=\{z\in\mathbb Z^2:R^2\le |z|^2\le(1+\eta)R^2\},
 \qquad \eta=(\log R)^{-1/4}.
\]

This set is centrally symmetric and has centroid zero. Unit-square lattice counting gives

\[
 |A_R|=\pi\eta R^2+O(R),
\]

and the same sums-of-two-squares upper bound gives

\[
 D(A_R)\ll R^2/\sqrt{\log R},\qquad
 D(A_R)/|A_R|\ll(\log R)^{-1/4}\longrightarrow0.
\]

Yet all squared centroid radii belong to `[R^2,(1+eta)R^2]`, so their relative standard deviation is at most `eta`, tending to zero. More generally, any prescribed positive relative thickness can coexist with arbitrarily large `n/D`, by taking `R` sufficiently large. This does not assert almost-regularity of the unweighted degree columns; it disproves only the inference from a small radial moment spread to linear distance support.

## 7. Precise conclusion and verification boundary

1. **Resolved negatively:** an absolute comparison `E>=c n I` in `D=o(n)`, even under the explicit condition `max_p I_p <= C I/n` for an absolute `C`. The counterexample also satisfies a matching lower bound at every pin and survives sparse vertex deletion.
2. **Not settled:** the separate amplification `(I+n^2)D^2>=c n^4`; no claim about it is inferred from the comparison counterexample.
3. **Not settled:** `ED^2>=c n^5` or the sharp planar Erdős lower bound. The construction is not claimed to be cardinality-maximal for its distance count.
4. A revised comparison would need a restriction on **which pins carry each color**, not merely exclusion of a sparse set of pins with large total isosceles mass. No such unproved restriction is offered as a solution.
5. `verify_pinned_degree_comparison.py` checks exact finite instances of the construction and the counting lemmas. Its output is saved in `pinned_degree_comparison_verification.txt`. All checks passed: 8,192 exact representation counts, 1,280 inert-prime identities, four full grids, five separated-block configurations, 120,128 ordered isosceles triples with endpoint-block and primitive-direction checks, additional translation/overlap tests, and three centroid annuli. The small block tests are **not** asserted to be in the low-distance regime; that regime is proved by (5.1) for the specified asymptotic parameters. The asymptotic theorem follows from the proofs above, not from extrapolation of those finite computations.
