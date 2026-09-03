# An actual-circular-order counterexample to the energy-adaptive pruning claim AP

## Status and main conclusion

**AP is false for full planar rectangular integer grids.** This is an asymptotic counterexample to capped *arc mass*, not merely to a raw second moment. It uses the complete pinned circle fibers and their actual circular orders.

For integers `H -> infinity`, let

\[
 t=\log H,\qquad L=\lceil Ht^{2/5}\rceil,\qquad
 P_H=\{0,\ldots,L-1\}\times\{0,\ldots,H-1\},\qquad n=LH.
\]

Write `D` for the number of positive squared distances, use the ordered-pair convention

\[
 r_s=|\{(p,q)\in P_H^2:|p-q|^2=s\}|,\qquad E=\sum_{s>0}r_s^2,
\]

and construct the arcs exactly as in the question: consecutive full-fiber circular gaps of angular length at most `pi`, one arc for a size-two fiber, none for a singleton. Let `mu_ab` be their unordered-endpoint multiplicities and `M_K=sum min(mu_ab,K)`.

Then

\[
 \boxed{D=o(n),\qquad |\mathcal A|=(1-o(1))n^2,}
\]

but, **for every fixed constant `C>0`**,

\[
 \boxed{\frac{M_{\lceil CE/n^3\rceil}}{n^2}\longrightarrow0.} \tag{1}
\]

In particular the required hypothesis `D <= (n-1)/2` holds for all sufficiently large `H`. Thus no absolute constants in AP can work.

The classical upper bound for the number of sums of two squares is the only number-theoretic input. The arc-capacity and rectangular energy estimates below are proved directly. This does **not** prove or refute the separate `M_{C log n} >= c n^2` assertion, and does not refute `ED^2 >= c n^5` or the sharp distinct-distance conjecture.

---

## 1. A finite actual-order lemma for every full rectangle

Throughout Sections 1--3 let `L >= H >= 2` be arbitrary integers, put

\[
 P=\{0,\ldots,L-1\}\times\{0,\ldots,H-1\},\qquad
 n=LH,\qquad \gamma=L/H.
\]

### Lemma 1: an empty minor arc cannot have nonsymmetric endpoints on opposite sides

Suppose a retained arc on a circle centered at `p in P` has endpoints `a,b` with

\[
 (a_x-p_x)(b_x-p_x)<0.
\]

Then `a_y=b_y`: its chord is horizontal.

**Proof.** Translate `p` to zero. The selected arc crosses one of the vertical rays from zero. Reflect the vertical coordinate if needed, so that this is the upward ray. If the circle radius is `R`, write the right and left endpoints respectively as

\[
 b=(R\sin\alpha,R\cos\alpha),\qquad
 a=(-R\sin\beta,R\cos\beta),
\]

where `0<alpha,beta<pi`. The selected arc's length in angle is `alpha+beta <= pi`.

If `alpha<beta`, the vertical-axis reflection

\[
 b'=(-R\sin\alpha,R\cos\alpha)
\]

is strictly inside this arc. Moreover

\[
 \sin\beta-\sin\alpha
 =2\cos((\alpha+\beta)/2)\sin((\beta-\alpha)/2)\ge0.
\]

Consequently `b'_x` lies between `a_x` and `0`. It is an integer, and `b'_y=b_y`. The full Cartesian rectangle therefore contains `b'`. It is a point of the same full circle fiber, contradicting consecutiveness. If `beta<alpha`, reflect `a` instead. Thus `alpha=beta`, giving equal endpoint heights. This also handles angular length exactly `pi`; no strict-minor assumption was used. QED.

This is the step that uses both actual circular order and the *full* rectangle. An arbitrary equal-radius pair need not satisfy the conclusion.

### Lemma 2: nonhorizontal large-radius arcs have narrow horizontal displacement

If a retained nonhorizontal arc has circle radius `R >= 2H`, then

\[
 \boxed{|a_x-b_x|\le H^2/R.} \tag{2}
\]

**Proof.** Write the endpoint coordinates relative to `p` as `(x_i,y_i)`. Since `|y_i|<=H-1<H`, the assumption on `R` implies `x_i!=0`. Lemma 1 makes their signs agree. The circle equations give

\[
 |x_1-x_2|
 =\frac{|y_2^2-y_1^2|}{|x_1|+|x_2|}
 \le\frac{H^2}{2\sqrt{R^2-H^2}}
 \le\frac{H^2}{\sqrt3 R}
 \le\frac{H^2}{R}.
\]

QED.

All centers are actual points of `P`, and all fibers here are the entire actual fibers. Nothing is inferred from a freely chosen order or a generic circle.

---

## 2. Finite capped-mass bound

### Proposition 3

For every integer `K>=1`, with the graph defined above,

\[
 \boxed{\frac{M_K}{n^2}\le
 7\frac{\sqrt K}{\gamma}+\frac K H.} \tag{3}
\]

The estimate is useful when `K=o(gamma^2)` and `K=o(H)`.

**Proof.** First choose any real radius cutoff `T>=2H`.

At a fixed pin, there are at most `(2T+1)H` grid points within distance less than `T`: their horizontal coordinates lie in an interval of length `2T`, and there are only `H` possible vertical coordinates. The graph on one fiber has at most as many arcs as vertices. Therefore all arcs with source radius `<T` number at most

\[
 N_{\rm near}\le 3nHT. \tag{4}
\]

Every remaining arc is either horizontal or, by (2), has endpoints satisfying `|a_x-b_x|<=H^2/T`. The number of unordered horizontal pairs is

\[
 N_{\rm horizontal}=H\binom L2\le nL/2.
\]

The total number of unordered pairs with horizontal displacement at most `H^2/T` is at most

\[
 N_{\rm narrow}
 \le \frac{nH}{2}(2\lfloor H^2/T\rfloor+1)
 \le nH^3/T+nH/2.
\]

For every endpoint pair,

\[
 \min(\mu^{\rm near}_{ab}+\mu^{\rm far}_{ab},K)
 \le \mu^{\rm near}_{ab}+K\,1_{\{\mu^{\rm far}_{ab}>0\}}.
\]

Summing and using `H<=L` proves

\[
 M_K\le3nHT+KnL+KnH^3/T. \tag{5}
\]

Set `T=2H sqrt(K)`. The first and third terms add up to `(13/2)nH^2 sqrt(K)`. Since `n=LH`, (3) follows, with `7` in place of `13/2`. QED.

This directly bounds the largest number of arcs in **any** subgraph of endpoint multiplicity at most `K`; that maximum is exactly `M_K`. No second-moment-to-first-moment inference is being made.

---

## 3. Elementary energy upper bound for a rectangular grid

### Proposition 4

There is an absolute constant `C_0` such that

\[
 \boxed{\frac E{n^3}\le
 C_0\left[1+
 \frac{(1+\log\gamma)(1+\log H)}{\gamma}\right].} \tag{6}
\]

**Proof.** Let

\[
 B=\{-(L-1),\ldots,L-1\}\times
   \{-(H-1),\ldots,H-1\},\qquad
 \rho_s=|\{z\in B:|z|^2=s\}|.
\]

An ordered difference vector `z=(x,y)` occurs exactly

\[
 w(z)=(L-|x|)(H-|y|)\le n
\]

times. Thus

\[
 E\le n^2 Q,\qquad
 Q=|\{(z,z')\in B^2:|z|^2=|z'|^2\}|. \tag{7}
\]

Including `z=z'=0` in `Q` only enlarges the bound.

For such a pair set `u=z+z'`, `v=z-z'`. Then `u dot v=0`, and both vectors have coordinate bounds `2L,2H`. Cases with `u=0` or `v=0` contribute `O(LH)`. The cases in which the nonzero perpendicular vectors are horizontal and vertical also contribute `O(LH)`.

In all other cases write

\[
 u=q(a,b),\qquad v=r(-b,a),
\]

where `(a,b)` is a primitive integer vector with nonzero coordinates, `q` is a positive integer, and `r` is a nonzero integer. Accounting for signs costs only an absolute factor. If `a,b` now denote their positive absolute values, the number of possible `q,|r|` is at most

\[
 \min(2L/a,2H/b)\min(2L/b,2H/a).
\]

Both `a,b<=2H` since both multipliers are nonzero. Dropping primitivity and parity only increases the upper bound. The expression is symmetric in `a,b`. On the half `a>=b`, it equals

\[
 \frac{4H^2}{a^2}\min(\gamma,a/b).
\]

For every `a>=1` and `gamma>=1`,

\[
 \sum_{b=1}^a\min(\gamma,a/b)\le a(1+\log\gamma). \tag{8}
\]

For example compare the decreasing summand with its integral on `[1,a]`, splitting at `a/gamma` if that point belongs to the interval. If `gamma>=a`, use `a(1+log a)<=a(1+log gamma)` instead.

It follows that

\[
 Q\le C\left[LH+H^2(1+\log\gamma)
                   \sum_{a=1}^{2H}\frac1a\right]
 \le C'\left[LH+H^2(1+\log\gamma)(1+\log H)\right]. \tag{9}
\]

Combine (7)--(9) and divide by `n^3=(LH)^3`. QED.

In particular this is an upper bound for the actual global color energy, with the ordered-pair convention in the supplied notes. It does not assume that colors are flat and does not use Guth--Katz.

---

## 4. The asymptotic counterexample

Return to

\[
 t=\log H,\quad L=\lceil Ht^{2/5}\rceil,\quad
 \gamma=L/H\asymp t^{2/5}.
\]

Every positive squared distance in `P_H` is a sum of two integer squares no larger than `2L^2`. The classical Landau--Ramanujan upper bound says

\[
 |\{1\le m\le X:m=x^2+y^2,\ x,y\in\mathbb Z\}|
 \ll X/\sqrt{\log X}.
\]

Since `log L~t`, this gives

\[
 \boxed{\frac D n\ll\frac{\gamma}{\sqrt t}
                \ll t^{-1/10}\longrightarrow0.} \tag{10}
\]

Hence the requested palette assumption holds eventually.

Let `F=sum_p |{s:k_{p,s}>0}|`. Every fiber of size `k` contributes at least `k-1` retained arcs: for `k>=3` at most one cyclic gap exceeds `pi`; the cases `k=1,2` are precisely the stated conventions. Consequently

\[
 n(n-1)-F\le|\mathcal A|\le n(n-1),\qquad F\le nD.
\]

By (10),

\[
 \boxed{|\mathcal A|=(1-o(1))n^2.} \tag{11}
\]

On the other hand (6) gives

\[
 \boxed{E/n^3\ll t^{3/5}\log t.} \tag{12}
\]

Fix any `C>0` and put `K_C=ceil(CE/n^3)`. For large `H`,

\[
 K_C\ll_C t^{3/5}\log t.
\]

Applying (3),

\[
 \frac{M_{K_C}}{n^2}
 \ll_C
 \frac{t^{3/10}\sqrt{\log t}}{t^{2/5}}
 +\frac{t^{3/5}\log t}{H}
 =O_C\left(t^{-1/10}\sqrt{\log t}
           +\frac{t^{3/5}\log t}{H}\right)
 \longrightarrow0. \tag{13}
\]

This proves (1). No lower estimate for `E` is needed: an upper bound on the proposed cap is the correct direction because `M_K` is nondecreasing.

More generally, `L=ceil(H (log H)^alpha)` works for every fixed

\[
 1/3<\alpha<1/2.
\]

The upper endpoint ensures `D=o(n)`; the lower endpoint ensures

\[
 (E/n^3)/\gamma^2
 \ll (\log H)^{1-3\alpha}\log\log H=o(1).
\]

### This is high-multiplicity mass, not a negligible exceptional second moment

For `K=K_C`,

\[
 \sum_{\mu_{ab}\le K}\mu_{ab}\le M_K=o(n^2).
\]

Together with (11), this implies

\[
 \boxed{\sum_{\mu_{ab}>K}\mu_{ab}=(1-o(1))n^2.} \tag{14}
\]

Thus almost all arcs lie on overloaded endpoint pairs at the AP cap. Deleting only an exceptional `o(n^2)` mass cannot repair AP. Every multiplicity-`K` subgraph has only `o(n^2)` arcs.

---

## 5. The counterexample also has a strong downward source-to-chord scale flow

There are at most two horizontal retained arcs on any one circle. Indeed each such arc has one of the two vertical rays from the center in its interior, while distinct consecutive gaps have disjoint interiors. Therefore horizontal arc mass is at most

\[
 2F\le2nD=o(n^2). \tag{15}
\]

Take `T=H t^{1/3}`. By (4), the mass of arcs with radius below `T` is

\[
 O(nHT)=O(n^2 t^{-1/15})=o(n^2).
\]

For each remaining nonhorizontal arc, let `s=R^2` be its source radius color and `d=|a-b|^2` its target chord color. Both belong to the same actual palette. Lemma 2 and `|a_y-b_y|<H` give

\[
 d\le H^2+H^4/R^2\le2H^2,
 \qquad s\ge H^2t^{2/3},
\]

so

\[
 \boxed{d/s\le2t^{-2/3}\longrightarrow0.} \tag{16}
\]

By (11), (15), and the near-radius bound, (16) applies to `(1-o(1))n^2` actual arcs. For fixed source color and unordered endpoints, the usual at-most-two-center property is also automatic in this family.

Thus even a very strong downward color-scale flow on almost all arc mass coexists with failure of AP. This does not refute every conceivable use of the hierarchy, but it prevents the hierarchy from implying AP as stated.

---

## 6. Scope, remaining questions, and verification boundary

1. **Resolved negatively:** the universal AP statement `M_ceil(CE/n^3) >= c n^2`, under the palette hypothesis in the question.
2. **Not resolved:** the separate cap-`C log n` statement. Here `gamma^2~(log H)^(4/5)`, whereas `log n~2 log H`; Proposition 3 therefore supplies no vanishing upper bound at that larger cap.
3. **Not refuted:** energy amplification `ED^2 >= c n^5` and the sharp distinct-distance conjecture. AP was only a proposed sufficient route to them.
4. The counterexample is an actual planar family, not an abstract color table, a single-fiber arrangement, a numerical extrapolation, or a reinstatement of the false uniform-per-chord or raw-second-moment claims discussed in the supplied notes.
5. No Lean files are changed. `verify_circular_order_rectangles.py` provides exact-integer sanity checks of the circular-order and counting lemmas. The asymptotic conclusion follows from the proofs above and the explicitly cited sums-of-two-squares bound, not from those checks.

The exact verification run passed on nine complete rectangles: 138,447 retained arcs, 75,331 opposite-side endpoint checks, 30,560 large-radius displacement checks, 568 nonaxis orthogonal-vector parameter checks, and 36 cap/cutoff checks. It also compared all actual ordered distance counts against the independent weighted-difference-vector formula. The output is saved in `circular_order_rectangular_grid_verification.txt`. These small rectangles test the lemmas, which hold for every `L>=H>=2`; they are not numerical representatives of the asymptotic low-palette regime.
