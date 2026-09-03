# Bias-centered multiplicative lifts: an arithmetic attempt

## Outcome and the first unproved inference

**This attempt does not settle Erdős #5.** It does obtain a genuine multiplicative decomposition of the centered lift, an arithmetic local parity gain, and an exact reduction retaining the globally prime-free interior. It does **not** infer a function-specific obstruction from the previously disproved uniform operator-norm bound.

The new local calculation is the following. If `p` is a pool prime, `p ∤ h`, and `v_p(hm)=1`, then

\[
 \mathbb E_{\mathbb Z_p}\!
 \left[(1_{p\mid n}-1/p)(-1)^{v_p(n)+v_p(n+hm)}\right]
 =-\frac{4(p-1)}{p^2(p+1)}.                                      \tag{L}
\]

Thus the **actual small-prime Liouville phase** supplies a local factor of order `p^(-2)`, not `p^(-1)`. For a squarefree label `m` these factors multiply under the unweighted local product measure. This is a real arithmetic gain, not an operator-norm assertion.

The first unproved inference in the attempted use of (L) is to replace that **unweighted local average** by the same average with the remaining multiplicative cofactor phases and the actual anchor weight attached. Section 5 defines the resulting remainder exactly. Complete multiplicativity does not make that remainder small, and the checked HR/MR results do not give its required relative bound. Even a bound for the full, unpinched bilinear form would need an additional argument to isolate the desired smooth-part block; a function-specific bound does not automatically survive pinching.

A second test uses the common anchor to average in `h` first. This is algebraically legitimate. But projecting the dense centered lift back to its rough endpoints changes the two oscillatory multiplicative functions into `R_y` and `R_y λ`, both vanishing at every small prime. The checked short-interval estimates do not give relative control of this projected sum at length `≍ log X`.

Everything below distinguishes exact identities, proved one-variable estimates, and unproved correlation estimates. No admitted Lean lemma was used. `Spec.lean` was not changed.

## 1. The one-point rough bias, with its size and error

Fix `1/3 < θ < 1/2`, put `y=X^θ`, and take `X` sufficiently large that `2X<y^3`. Write

- `R_y(n)=1` if `n>1` and every prime factor of `n` exceeds `y`;
- `P(n)=1_Prime(n)`;
- `λ(n)=(-1)^Ω(n)`.

On `(X,2X]`, every rough number has `Ω=1` or `2`. Squares have `Ω=2` and are included. Therefore

\[
 P(n)=R_y(n)\frac{1-\lambda(n)}2.                              \tag{1}
\]

This identity is being asserted on this range, not for primes below `y`.

Let `P_X` count primes in `(X,2X]` and `S_X` count rough semiprimes there, with each integer counted once. PNT and an ordered two-prime sum give

\[
\begin{aligned}
 P_X&=\frac X{\log X}+O_\theta\!\left(\frac X{\log^2X}\right),\\
 S_X&=c_\theta\frac X{\log X}
          +O_\theta\!\left(\frac X{\log^2X}\right),
 \qquad c_\theta=\log\frac{1-\theta}{\theta}.                  \tag{2}
\end{aligned}
\]

For the second formula, the main ordered sum is

\[
 \frac X2\int_y^{X/y}\frac{dt}{t\log t\log(X/t)}
 =\frac X{2\log X}\int_\theta^{1-\theta}\frac{du}{u(1-u)}
 =c_\theta\frac X{\log X}.
\]

The range `X/y<p≤2X/y`, the dyadic changes inside logarithms, and the PNT approximation contribute `O_θ(X/log²X)`. Correcting the ordered count on squares costs `O(√X)`, smaller than this error. No two-shift prime assertion is used here.

Define

\[
 \rho=\frac1{1+c_\theta},\qquad
 \mu_\theta=1-2\rho=\frac{c_\theta-1}{1+c_\theta},\qquad
 b_y(n)=P(n)-\rho R_y(n)\quad (X<n\leq2X).
\]

Then

\[
 b_y=\frac12R_y(\mu_\theta-\lambda),\qquad
 \sum_{X<n\leq2X}b_y(n)=O_\theta(X/\log^2X).                  \tag{3}
\]

The unconditioned rough Liouville mean is `μ_θ`, **not zero**. Centering corrects this main term. It does not make a conditional two-point mean zero.

There is also an exact finite centering option:

\[
 \rho_X:=\frac{P_X}{P_X+S_X}=\rho+O_\theta(1/\log X).
\]

Using `ρ_X` makes the one-point sum exactly zero. On a desired weighted rough-pair sum of mass `M`, changing `ρ` to `ρ_X` changes the centered sum by exactly `(ρ-ρ_X)M`, hence `O_θ(M/log X)`. Thus the leading-constant error is not the essential difficulty. This relative statement concerns the **rough-pair sum**, not an arbitrary unisolated graph sum.

The centered second moment is still on the one-prime scale:

\[
 \sum_{X<n\leq2X}|b_y(n)|^2
 =\bigl((1-\rho)^2+\rho^2c_\theta+o(1)\bigr)\frac X{\log X}
 =\bigl(1-\rho+o(1)\bigr)\frac X{\log X}.                    \tag{4}
\]

For fixed `θ`, this saves a constant, not a factor `log X`.

## 2. Exact multiplicative lifts, including the omitted cases

For **all positive integers**, let `s=s_y(n)` be the full `y`-smooth part, including powers, and let `r=r_y(n)=n/s`. Introduce three completely multiplicative functions:

\[
 S_y(n)=\lambda(s_y(n)),\qquad L(n)=\lambda(n),\qquad
 Z_y(n)=\lambda(n)1_{r_y(n)=1}.                               \tag{5}
\]

Their prime values are

| function | `p≤y` | `p>y` |
|---|---:|---:|
| `S_y` | `-1` | `+1` |
| `L` | `-1` | `-1` |
| `Z_y` | `-1` | `0` |

Define the actual prime-cofactor lift and the centered lift that vanishes at rough cofactor `1`:

\[
 F_y(n)=\lambda(s)P(r),\qquad
 G_y(n)=\lambda(s)\bigl(P(r)-\rho 1_{r>1}\bigr).               \tag{6}
\]

Let

\[
 O_y(n)=1_{\Omega(r_y(n))\geq3\text{ and odd}}.
\]

Since, for every positive `r`,

\[
 P(r)=\frac{1-\lambda(r)}2
      -1_{\Omega(r)\geq3\text{ and odd}},
\]

we have the following **global exact identities**:

\[
\boxed{\begin{aligned}
 F_y&=\tfrac12(S_y-L)-S_yO_y,\\
 G_y&=(\tfrac12-\rho)S_y-\tfrac12L+\rho Z_y-S_yO_y.
\end{aligned}}                                               \tag{7}
\]

### The rough cofactor `r=1`

For the literal, uncut lift in the question,

\[
 G_y^{\rm all}(n)=\lambda(s)\bigl(P(r)-\rho\bigr),
\]

the formula is instead

\[
 G_y^{\rm all}=(\tfrac12-\rho)S_y-\tfrac12L-S_yO_y.            \tag{8}
\]

**At `r=1`, the two-term formula (8) is already correct:** both sides equal `-ρλ(n)`. There is no identity error there. The issue is support: if the intended lift is zero there, one must add `+ρZ_y`, as in (7).

This is not a negligible exceptional set on a dense lift. For fixed `log N/log y`, the `y`-smooth integers in a dyadic interval of scale `N` have positive Dickman density. In particular, `|Z_y|²` has positive mean. Its signs do not justify deleting it after an endpoint mask. On the desired top blocks the cofactor is large and `Z_y` vanishes, but this is an exact support restriction, not a small-error argument for the full graph.

### Rough cofactors with three or more factors

If every inspected integer is below `y³`, then `O_y=0` identically. This remains valid for lifts of the original range by `m≤X^{o(1)}`: eventually `3Xm<y³`, because `3θ>1` has a fixed margin. Likewise it holds on `(N,2N]` with `y=N^θ`, including zero-extended displacements of size `N^{o(1)}` when the inspected range is enlarged to `3N`.

If this range condition is dropped, `-S_yO_y` must be retained. It is not a vaguely bounded error. Odd rough factor counts `3,5,...` are precisely the correction; even counts `4,6,...` need none in the algebraic identity.

### Complete multiplicativity really is available

For any pool product `d` whose prime factors are at most `y`, with no coprimality condition between `d` and `n`,

\[
 F_y(dn)=\lambda(d)F_y(n),\qquad
 G_y(dn)=\lambda(d)G_y(n).                                   \tag{9}
\]

For a fixed anchor function `e` on rough cofactors, including `e(1)=0`,

\[
 F_e(n):=S_y(n)e(r_y(n))
 \quad\Longrightarrow\quad F_e(dn)=\lambda(d)F_e(n).          \tag{10}
\]

Thus the anchor does not destroy **small-prime multiplicative transport**. It is nevertheless not a completely multiplicative function on all integers, and (10) does not imply additive independence of that anchor.

There is a useful whole phase family. Put

\[
 A_z(n)=z^{\Omega(s_y(n))},\quad
 L_z(n)=z^{\Omega(s_y(n))}\lambda(r_y(n)),\quad
 Z_z(n)=z^{\Omega(n)}1_{r_y(n)=1}.
\]

All three are completely multiplicative: their small-prime value is `z`, and their large-prime values are `1,-1,0`, respectively. Below `y³`,

\[
 z^{\Omega(s)}(P(r)-\rho1_{r>1})
   =(\tfrac12-\rho)A_z-\tfrac12L_z+\rho Z_z.                 \tag{11}
\]

At `z=-1` this is (7). Hence the arithmetic structure is genuine, rather than an arbitrary sparse marking disguised as a multiplicative function.

There is also a direct prime-distance check. With the usual quantity
`D(f,g;N)²=Σ_{p≤N}(1-Re(f(p)conj(g(p))))/p`, at `y=N^θ` the prime-value table and Mertens' estimate give

\[
 D(S_y,\lambda;N)^2=2\log(1/\theta)+o(1),\qquad
 D(Z_y,\lambda;N)^2=\log(1/\theta)+o(1).
\]

So these dense functions differ from Liouville on only bounded reciprocal-prime mass. This is useful arithmetic information about the actual phases; it is not a claim that a dense non-pretentiousness or mean-value estimate persists after rough projection or gap conditioning.

Two cautions about centering remain:

1. `ρ` centers rough numbers at scale `X`. It need not center every cofactor scale in a fully dense lift. Indeed the sum of (6) is a sum over smooth `s` of
   `λ(s)[P_y(N/s,2N/s)-ρ R_y(N/s,2N/s)]`. When the rough cofactor lies below `y²`, every nontrivial rough cofactor is prime, with prime fraction `1`, not `ρ`.
2. On subpower top blocks `T=N/m`, `m≤N^{o(1)}`, the effective parameter is `θ_T=log y/log T`. Uniformly there,
   `ρ(θ_T)-ρ(θ)=O_θ(log m/log N)`. This is `o(1)`, and changing it in an already isolated rough-pair sum costs `o(M)`. A cofactor-dependent coefficient would, however, no longer be a constant linear combination of the three multiplicative functions in (7). It cannot be inserted into a dense multiplicative theorem without analysis.

## 3. The eventual missing band gives an exact common anchor

Let `p_i` be the globally ordered primes and `g(p_i)=p_{i+1}-p_i`. Suppose, for the purpose of contradiction, that the normalized gaps eventually avoid a fixed band `(a,b)`, and choose fixed `a<A<B<b`, with `A>0`.

PNT gives, uniformly for `p_i∈(X,2X]`,

\[
 \log i=\log X-\log\log X+O(1).
\]

Consequently the fixed margins ensure that, for large `X`, any gap between `A log X` and `B log X` would lie in the forbidden index-normalized band. Set

\[
 \mathcal H_X=\{h\in\mathbb Z:A\log X<h<B\log X\},
 \qquad
 E_X=\{X<p\leq2X-B\log X:g(p)>A\log X\}.                    \tag{12}
\]

Then for every prime in the displayed anchor range and every `h∈H_X`,

\[
 \boxed{\quad
 \prod_{1\leq j<h}(1-P(p+j))=1_{E_X}(p),\qquad
 p\in E_X\ \Longrightarrow\ P(p+h)=0.
 \quad}                                                     \tag{13}
\]

Proof: if `g(p)≤A log X<h`, the next prime is in the interior. If `g(p)>A log X`, the missing band forces `g(p)≥B log X>h`. The equality uses the **true interior**, not a sieve proxy. The endpoint cannot be the next prime in the forbidden band. There is no endpoint off-by-one loss.

The common anchor has another concrete consequence: its forward windows are disjoint. If `p<p'` belong to `E_X`, then `p'≥p+g(p)≥p+B log X`. Thus the sets `p+H_X` do not overlap. Under the missing-band assumption the union is a genuine union of prime-free windows, not an arbitrary edge mask.

Define exact counts

\[
\begin{aligned}
 N_X&=\sum_{p\in E_X}\sum_{h\in\mathcal H_X}P(p+h),\\
 T_X&=\sum_{p\in E_X}\sum_{h\in\mathcal H_X}
         1_{\Omega(p+h)=2}R_y(p+h),\\
 M_X&=N_X+T_X
      =\sum_{p\in E_X}\sum_{h\in\mathcal H_X}R_y(p+h),\\
 D_X&=\sum_{p\in E_X}\sum_{h\in\mathcal H_X}b_y(p+h).
\end{aligned}
\]

All endpoints are in `(X,2X]`, so (1) applies, and

\[
 \boxed{D_X=N_X-\rho M_X
       =\rho(c_\theta N_X-T_X).}                            \tag{14}
\]

Under the missing band,

\[
 N_X=0,\qquad D_X=-\rho M_X=-\rho T_X.                       \tag{15}
\]

Therefore a relative estimate `|D_X|=o(M_X)` on scales with `M_X>0` would give a contradiction. A weaker suitable one-sided estimate would suffice. **Neither positive mass nor this relative estimate is asserted here.** An absolute `o(X)` estimate does not suffice: the usual averaged pair benchmark is `X/log X`, and may be much smaller if the anchors are scarce.

For comparison, the ordinary two-dimensional upper-bound sieve gives, for even nonzero `h=O(log X)`,

\[
 \sum_{X<p\leq2X}R_y(p+h)
 \ll_\theta\frac X{\log^2X}
 \prod_{\substack{\ell\mid h\\\ell>2\ {\rm prime}}}
                  \frac{\ell-1}{\ell-2}.
\]

One may sieve only to a sufficiently small fixed power of `X`, below `y`, to obtain this upper bound. Odd `h` give zero. The singular factors have bounded average: expand their product into squarefree divisors and use the convergent product `∏_{ℓ>2}(1+1/(ℓ(ℓ-2)))`. Thus `M_X≪_θ X/log X`. This is an upper bound, **not** a positive-mass theorem for `E_X`.

## 4. The actual centered displacement transport

Use a pool `P⊂[H_0,H]` with `H<y`; let `M_k(P)` be the unordered squarefree `k`-prime products, and `E_k=Σ_{m∈M_k}1/m`. Take `k≥1` and `h>0`, coprime to the pool. For the numerical budgets use the audited example

```
log H=(log N)^(2/5),  log H_0=(log N)^(3/10),
P={primes in [H_0,H]},  k=O(log log N).
```

Then `L=Σ_{p∈P}1/p∼(1/10)log log N`, `max m=N^{o(1)}`, and `H_0` exceeds every fixed power of `log N`. In particular every `h∈H_N` is eventually coprime to the pool.

Write

\[
 c_m(n)=\prod_{p\mid m}(1_{p\mid n}-1/p).
\]

Let `W∈{0,1}` be an endpoint mask supported on `V=(N,2N]`, and take the actual anchor `e∈{0,1}`. The lifts remain defined on **all positive integers**; only the compressed vertex functions `WF` and `WG` are zero-extended. It is helpful to display the positive orientation

\[
 \mathcal B^+_{k,h}(F,G;W)
 =\frac1N\sum_{m\in M_k}\sum_n
 W(n)W(n+hm)c_m(n)F(n)G(n+hm).                              \tag{16}
\]

The symmetric `B_k` is the sum of the two orientations; for the negative orientation replace `h` by `-h` and omit nonpositive arguments. No power of the order-one graph is used.

Taking `F=F_e`, `G=G_y`, expansion of the centered divisor product and (9)–(10) give the exact formula

\[
\boxed{
 \mathcal B^+_{k,h}(F_e,G_y;W)
 =\sum_{j=0}^k(-1)^{k-j}
 \sum_{\substack{d\in M_j,\ e'\in M_{k-j}\\(d,e')=1}}
 \frac1{e'}\frac1N\sum_{u\geq1}
 W(du)W(d(u+he'))F_e(u)G_y(u+he').}                          \tag{17}
\]

All boundary and anchor conditions remain. The mask is `W(du)`, not `W(u)`; the values `F_e(u)` and `G_y(u+he')` are the global lifts, not their restrictions to `V`. The two small-prime factors are `λ(d)²=1`. In particular the real phase `-1` does **not** create another sign depending on `j` that could cancel the proper-divisor terms formally.

By (7), whenever the inspected range is below `y³`,

\[
 \mathcal B^+(F_e,G_y;W)
 =(\tfrac12-\rho)\mathcal B^+(F_e,S_y;W)
 -\tfrac12\mathcal B^+(F_e,L;W)
 +\rho\mathcal B^+(F_e,Z_y;W).                              \tag{18}
\]

This exact identity is the legitimate place to try a phase-specific estimate for actual multiplicative functions. It does not make its three bilinear terms independent or small.

There is also a geometry issue beyond algebra: an off-top edge in (17), with `u=sp`, has right endpoint `sp+he'`, whose rough cofactor need not be `p+h`. The original missing band constrains the latter shift, not every affine cofactor pair generated by (17). The multiplicative invariance of the left anchor must not be mistaken for preservation of the desired gap on all these edges.

### What survives exact top pinching

Project both endpoints onto the same exact smooth part `s∈M_k(P)`. Since `s|hm` and `(h,∏P)=1`, equality of the smooth parts forces `s|m`; the two labels have the same number of prime factors, so `s=m`. On that block, for rough `r,r+h`,

\[
 c_m(mr)=\frac{\varphi(m)}m,\qquad
 F_e(mr)G_y(m(r+h))
 =e(r)\bigl(P(r+h)-\rho\bigr).                              \tag{19}
\]

Consequently the exact pinched form is

\[
 \frac1N\sum_{m\in M_k}\frac{\varphi(m)}m
 \sum_{\substack{r\geq1\\r,r+h\;y\text{-rough}}}
 W(mr)W(m(r+h))e(r)\bigl(P(r+h)-\rho\bigr).                 \tag{20}
\]

For `e=1_{E_X}`, this retains precisely the original anchor and shift, wherever the explicit endpoint masks allow them. If using a common ambient dyadic interval, its cofactor ranges are **exactly** `(N/m,2N/m]`. One can instead use an anchor on the union of those ranges with threshold `A log N`; since `log(N/m)=(1+o(1))log N`, the same fixed missing-band margins apply. These two choices are not silently identified with the single interval `(X,2X]`.

Notice what the actual phase did on the desired block: `λ(m)` appeared at each endpoint and **canceled exactly**. There is no remaining small-prime oscillation inside that block. This does not rule out cancellation from the rough-cofactor parity; it identifies the parity that must still be estimated.

For the unanchored top lifts on `(N,2N]`, with `y=N^θ` and `max m=N^{o(1)}`, single-integer counting yields

\[
 \|F_y^{[k]}\|_2^2=(1+o(1))\frac{E_k}{\log N},\qquad
 \|G_y^{[k]}\|_2^2=(1-\rho+o(1))\frac{E_k}{\log N}.           \tag{21}
\]

The second formula uses (4) at the cofactor scales. The transported pair benchmark is `E_k/log²N`. Centering improves the norm cost by a fixed constant only. No false small uniform norm is being proposed.

A separate logical warning is important here. Although pinching is contractive for an **operator norm**, a small value of the particular unpinched form `⟨F_e,B_kG_y⟩` does not imply a small value after pinching. Opposite contributions from unequal smooth parts may have canceled in the former. A bound only at phase `z=-1` also does not permit averaging arbitrary prime phases to project onto an exact smooth part. Thus proving (18) small would not, by itself, prove (20) small.

## 5. A new local parity calculation and the exact unresolved remainder

This section exploits actual multiplicativity rather than postulating a spectral estimate.

For a prime `p`, put `u_p(n)=(-1)^{v_p(n)}` on `Z_p` outside the measure-zero point `0`. For `p∤a`, the two residues `n≡0,-a (mod p)` are disjoint. Summing their valuation distributions gives

\[
 \mathbb E[u_p(n)u_p(n+a)]
 =1-\frac2p+
       2\frac{p-1}{p}\sum_{j\geq1}\frac{(-1)^j}{p^j}
 =1-\frac4{p+1}.                                           \tag{22}
\]

Now suppose the displacement is `pa`, with `p∤a`. Conditional on `p∤n`, the local phase is `1`. Conditional on `p|n`, substitute `n=pv`; the two additional factors `-1` cancel and the conditional mean is (22). Therefore

\[
\begin{aligned}
 \mathbb E[u_p(n)u_p(n+pa)]&=1-\frac4{p(p+1)},\\
 \mathbb E[(1_{p\mid n}-1/p)u_p(n)u_p(n+pa)]
 &=\frac1p(1-\tfrac1p)
       \left(1-\frac4{p+1}-1\right)\\
 &=-\frac{4(p-1)}{p^2(p+1)}=:\kappa_p.                     \tag{23}
\end{aligned}
\]

This computes exactly the local parity effect of the centered divisor factor. It includes higher powers of `p`; discarding them would miss the first nonzero covariance. For comparison, the centered divisor factor alone has mean zero. Thus (23) is not an improvement on zero: it quantifies the bias introduced by the real parity phase and shows that it is only of order `p^(-2)`, compared with absolute edge-weight mass of order `p^(-1)`. It is not yet a weighted correlation estimate.

For squarefree `m`, let

\[
 U_m(n)=\prod_{p\mid m}u_p(n),\qquad
 K_{m,h}(n)=c_m(n)U_m(n)U_m(n+hm).
\]

When `(h,m)=1`, independence of the local coordinates under product Haar measure gives

\[
 \kappa_m:=\mathbb E_{\prod_{p\mid m}\mathbb Z_p}K_{m,h}
    =\prod_{p\mid m}\kappa_p.                              \tag{24}
\]

This is a statement about the unweighted local product measure. It is not a distribution statement for a prime anchor.

### Stripping off the local phases of the actual lifts

There is an exact way to see what is missing. Define

\[
 F_e^{(m)}(n)=U_m(n)F_e(n),\qquad
 G_y^{(m)}(n)=U_m(n)G_y(n).
\]

The signs at primes dividing `m` have been removed. Below `y³`, `G_y^{(m)}` is still a linear combination of three actual completely multiplicative functions, now with value `+1` at those primes. The cofactor anchor remains attached to `F_e^{(m)}`. Set

\[
 w_{m,h}(n)=W(n)W(n+hm)F_e^{(m)}(n)G_y^{(m)}(n+hm).
\]

Then (16) is **exactly**

\[
\begin{aligned}
 \mathcal B^+_{k,h}(F_e,G_y;W)
 &=\sum_{m\in M_k}\kappa_m\frac1N\sum_n w_{m,h}(n)
       +\mathcal R_{k,h},\\
 \mathcal R_{k,h}
 &:=\frac1N\sum_{m\in M_k}\sum_n
       (K_{m,h}(n)-\kappa_m)w_{m,h}(n).                     \tag{25}
\end{aligned}
\]

The explicit local-mean part really is tiny. Since `|w_{m,h}|≤1` and `W` is supported on an interval of length `N`,

\[
 \left|\sum_m\kappa_m\frac1N\sum_nw_{m,h}(n)\right|
 \leq\sum_m|\kappa_m|
 \leq4^k\sum_m\frac1{m^2}
 \leq(4/H_0)^k E_k.                                       \tag{26}
\]

In the stated pool regime, this is `o(E_k/log²N)` already for `k=1`. The same bound holds after averaging over `h∈H_N`. This is a proved phase calculation, not the false normalized operator bound.

**The first failed inference would now be:** because the external factors in `w_{m,h}` come from multiplicative functions, conclude

\[
 \left|\frac1{|\mathcal H_N|}
          \sum_{h\in\mathcal H_N}\mathcal R_{k,h}\right|
       =o(E_k/\log^2N).                                   \tag{27 — NOT PROVED}
\]

There is no such implication. Removing the valuation sign at `p` does not remove dependence on `n mod p^j`: on a residue with `p|n`, the other prime factors are those of a rescaled integer, and at the other endpoint they are those of a differently shifted cofactor. The anchor `e(r_y(n))` also varies with these cofactors. CRT supplies (24), but does not factor this arithmetic weight out of the local average.

This is not merely an unspecified appeal to “cancellation after a mask”: (25) specifies the exact weight and the exact remainder that would have to cancel. It retains the original displacements `hm`, the actual multiplicative phases, and the actual pulled-back anchor. Neither a one-point rough count nor the identity (7) estimates it.

Also, even proving (27) for the full form would leave the isolation issue described after (21). The corresponding **pinched** remainder contains the short-shift rough parity problem itself. On (19), each label prime divides both endpoints to exponent exactly one; the phase product is fixed, not distributed according to (22). Transferring (27) to this conditional set would require another genuinely arithmetic estimate.

Nothing here asserts that (27), or a more appropriately structured relative estimate, is false for the actual arithmetic weights. The calculation identifies precisely the inference not supplied by the available inputs.

## 6. Testing the common-`h` route against actual short-interval theorems

The common anchor does permit the following useful exact rearrangement:

\[
 D_X=\sum_n1_{E_X}(n)\sum_{h\in\mathcal H_X}b_y(n+h).         \tag{28}
\]

There is now only a left endpoint weight, independent of `h`. In particular it would be wrong to reject this step merely because the original interior mask depended on the displacement.

### Where the dense multiplicative decomposition stops helping directly

Let `\widetilde R_y` be the completely multiplicative rough indicator, including `\widetilde R_y(1)=1`. For `n>1` in the target range,

\[
 \widetilde R_y(n)S_y(n)=\widetilde R_y(n),\qquad
 \widetilde R_y(n)Z_y(n)=0,
\]

and hence

\[
 \boxed{\quad
 b_y(n)=\widetilde R_y(n)G_y(n)
       =(\tfrac12-\rho)\widetilde R_y(n)
                    -\tfrac12\widetilde R_y(n)\lambda(n).
 \quad}                                                     \tag{29}
\]

The prime term in the definition of `\widetilde R_yG_y` is the indicator of primes exceeding `y`; on `(X,2X]` it is simply `P(n)`. The displayed two-term formula is restricted to the target range. Outside the `y³` range the odd-`Ω` correction from (7) returns.

Thus rough projection removes the small-prime negative phases of the dense functions in (7). Both functions on the right of (29) vanish at all primes `≤y`. The non-vanishing hypothesis in the sparse MR theorem fails for every fixed positive parameter `α`: taking a growing prime interval below `y` gives a zero left side in that hypothesis and a positive divergent reciprocal-prime sum on the right.

The dense MR theorem still applies to these functions, but its **absolute** error is larger than their entire mean `≍1/log X`. That is not a relative theorem for rough numbers.

### The dense functions themselves are legitimate MR inputs

There is no objection based merely on the fact that `S_y` depends on `X`. The original MR theorem is uniform in real `[-1,1]`-valued multiplicative functions. It applies separately to `S_y`, `L`, and `Z_y`; taking a linear combination gives a valid statement about unprojected averages of `G_y`, around their actual long mean.

The quantitative limitation matters. The checked improved dense theorem gives an error including

\[
 \delta+C'\frac{\log\log H}{\log H}
                +(\log X)^{-\eta/36},
 \qquad \eta<1/3-2/(3\pi),
\]

outside a set of size

\[
 \ll_\eta X\left(H^{-\delta/15}
                 +X^{-\delta^4/10^{16}}\right),
 \qquad 0<\delta<1/1000.                                   \tag{30}
\]

At `H≍log X`, this does not provide an `o(1/log X)` error. Even the displayed exceptional-set upper bound can exceed the entire prime-anchor population `≍X/log X`. This is an insufficiency of the bound, not a claim that the actual exceptional set contains the anchors.

The disjoint prime-free windows from Section 3 give more structure than an arbitrary sparse set, but absence of primes in those windows does not force a fixed sign for the **dense** `G_y`. Integers with nontrivial smooth part contribute both signs. Deleting those contributions returns (29). Thus thickening the anchors into windows does not by itself turn a dense MR statement into the required rough-parity statement.

A direct Cauchy–Schwarz attempt makes the missing relative scale explicit. For this calculation only, zero-extend `b_y` from `(X,2X]` to all integers. This does not change (28). With

\[
 A_X(n)=\frac1{|\mathcal H_X|}\sum_{h\in\mathcal H_X}b_y(n+h),
\]

we have

\[
 |D_X|\leq |\mathcal H_X|\,|E_X|^{1/2}
                      \left(\sum_n|A_X(n)|^2\right)^{1/2}. \tag{31}
\]

Even in the favorable benchmark `|E_X|≍X/log X`, `M_X≍X/log X`, a sufficient whole-integer mean-square estimate from (31) would be

\[
 \sum_n|A_X(n)|^2=o(X/\log^3X),                             \tag{32 — NOT PROVED}
\]

not just `o(X)`. Expanding this mean square introduces correlations of the **rough-centered** function at short shifts. Its diagonal contribution is of order `X/log²X` by (4) and `|H_X|≍log X`; off-diagonal terms can have either sign, so this is not being advertised as a rigorous lower bound for the whole second moment. It does show why an ordinary absolute mean-square estimate is not the promised relative input. An actual anchor-specific bilinear estimate could be better than (31), but is precisely what remains unproved.

### Damping the phase does not produce a free short-average regime

The family (11) also permits `z=-t`, `0<t≤1`. Its two principal multiplicative functions have absolute prime value `t` below `y` and `1` above `y`. The interval-length parameter in the checked sparse MR theorem is

\[
 H(f;X)=\prod_{p\leq X}\left(1+\frac{(|f(p)|-1)^2}{p}\right)
       \asymp_\theta(\log X)^{(1-t)^2}.                    \tag{33}
\]

For fixed `t>0`, this can be useful for dense damped averages, but does not project onto the zero-smooth-part component. The natural choice `t≍1/log log X`, keeping the smooth harmonic Euler product
`∏_{p≤y}(1-t/p)^(-1)≍(log y)^t` bounded, makes (33) comparable to `log X`. At the desired length `C log X`, the remaining MR length parameter `h_0=H/H(f;X)` is then bounded, rather than tending to infinity. In addition its non-vanishing parameter would tend to zero, outside a uniform fixed-`α` application of the theorem. This is another concrete reason not to infer a relative rough estimate from the multiplicative phase family.

### What HR actually adds, and what it does not

The checked HR main theorem and `cor:maic` concern the centered **prime-displacement, order-one** operator. Their normalized bilinear error is `O(L^(-1/2))` after the permitted norm scaling. The Liouville comparison `cor:notmarat` genuinely allows an arbitrary bounded left function against an unmasked translated `λ` on the right. This is useful and should not be dismissed as an arbitrary-mask prohibition.

However:

- it is a long prime-displacement comparison, not a relative theorem for `R_yλ` under (29);
- the printed theorem is not a theorem for `B_k` with composite displacement `hm`;
- the fixed growing shift and the remaining cofactor masks in (25) are not removed by the corollary;
- even granting a favorable growing-`h` extension of an order-one bound `O(√L)`, the actual `k=1` top lifts in (21) give an unnormalized form budget `O(√(1-ρ)L^(3/2)/log N)`. Dividing by the transported degree `L` leaves `O(√(1-ρ)√L/log N)`, against the normalized pair benchmark `1/log²N`. This calculation keeps the lift mass `E_1=L`; it does not silently treat those lifts as having squared norm `1/log N`.

The last item is just an error-budget check. It is not an asserted lower bound for the actual centered bilinear form. The local gain (23) is a different possible source of improvement, but HR's existing uniform estimate does not establish its weighted remainder (27).

## 7. The remaining arithmetic is an actual prime/semiprime correlation

The common-anchor semiprime term has an explicit factorization:

\[
 T_X=
 \sum_{\substack{y<q\leq r\\q,r\ {\rm prime}\\X<qr\leq2X}}
       \sum_{h\in\mathcal H_X}1_{E_X}(qr-h).                 \tag{34}
\]

The indicator automatically imposes all anchor endpoints and the true initial prime-free segment. Squares occur once. Since `q>y≫|H_X|`, for a given anchor and `q` there is at most one `h` in the band with `q|(p+h)`. Thus (34) has meaningful multiplicative structure; it is not an arbitrary signed coloring.

But (34) still asks about primes `p=qr-h`, with the future-gap condition on `p`, correlated with two large prime factors `q,r`. One-point PNT, or distribution of unconditioned primes in progressions, is not a distribution theorem for this future-gap-selected prime set. In particular it does not prove

\[
 T_X=c_\theta N_X+o(M_X),                                  \tag{35 — NOT PROVED}
\]

which by (14) is exactly the desired centered conclusion. Under the missing band (35) would force the positive rough-composite mass to disappear; it cannot be credited merely because `c_θ` was computed correctly in (2).

This identifies the arithmetic target left after centering: a conditional prime-versus-semiprime balance, retaining `h≍C log X`, not a uniform mixing theorem on all graph vectors.

## 8. Error ledger, verification, and sources

### Errors and exceptional cases accounted for

- **`r=1`:** (8) holds there as written for the uncut lift. For a lift vanishing there, the exact correction is `+ρZ_y`. It is not discarded on dense support.
- **`Ω(r)≥3`:** the exact global correction is `-S_yO_y`. It vanishes on the stated inspected ranges, including subpower lifts, by `y³` exceeding their upper endpoint.
- **Prime powers:** included in `s_y` and in the parity calculation (22)–(23). Rough squares have the composite sign and are counted once.
- **One-point bias approximation:** (2) has an `O(X/log²X)` error. Exact empirical centering is available; its effect on the desired correlation is `O(M_X/log X)`, not an unquantified dense error.
- **Scale changes:** the cofactor interval in (17) and (20) is retained exactly. Fixed margins transfer the missing band from `log(index)` to the indicated `log X` or `log N` scales; varying cofactor prime fractions are not silently treated as equal on a fully dense lift.
- **Boundaries and integer shifts:** endpoint masks are retained in every graph identity. `H_X` is the exact integer set in (12); no endpoint shift is discarded using a pair-count heuristic.
- **Multiplicative versus additive graphs:** `B_k` is never identified with `(U-Q)^k`. No new uniform normalized norm bound is asserted.
- **Positive mass:** no lower bound for `M_X` on the selected anchors is assumed. A complete contradiction would require it, or another genuine existence argument, in addition to relative parity control.

### Exact finite verification

`Submission/check_bias_centered_lift.py` uses integer factorization and rational arithmetic. Running it produced:

```
PASS: 24000 full lift identities (including r=1 and odd Omega>=3)
PASS: 7200 complete-multiplicativity checks
PASS: 12 masked real-phase transports; 12 exact top blocks
PASS: 12 exact local-mean/remainder splits and budgets (10 nonzero remainders)
PASS: 70 local parity covariances; 3 composite CRT products
PASS: 18 common-anchor masks; nonzero centered composite mass -7/11
```

The local calculation is checked exactly modulo `p²`, assigning the zero residue its conditional Haar mean `(p-1)/(p+1)`, rather than pretending higher valuations do not exist. The arithmetic weights in the finite graph tests give nonzero remainders in 10 of 12 cases; this confirms that factoring out the local mean is not an exact weighted identity. No asymptotic lower bound for those remainders is inferred. The common-anchor check uses a finite interval with an actual missing band and anchor `113`; the interior rough composite `121=11²` makes the centered mass nonzero. This is a check of the finite identities, not evidence of an eventual missing band or of an asymptotic estimate.

### Sources actually checked

Only the two requested prior audits were read, not the other attempt reports:

- `Submission/CenteredCompositeTransportAudit.md`, especially Sections 1–2 and its scope statement;
- `Submission/HelfgottRadziwillAudit.md`, especially Sections 1, 4, and 6.

The source passages checked were:

- `/corpus/src/2103.06853/trace.tex`: main theorem and `cor:maic`, lines 186–265; factor-count transport, 325–384 and 6442–6510; parity consequences, 389–434; actual translated-Liouville comparison `cor:notmarat`, 6350–6420; composite-edge discussion, 7505–7562. The latter is a proposal, not a proved composite-edge theorem.
- `/corpus/src/1501.04585/ShorterIntervals55.tex`: uniform real multiplicative short-average theorem, lines 29–42.
- `/corpus/src/1503.05121/intro.tex`: averaged Chowla and exponential-sum statements, particularly lines 28–51. Its discussion explicitly distinguishes dense cancellation from localization to rough numbers/primes.
- `/corpus/src/2007.04290/Vanishing27.tex`: improved dense theorem, lines 266–280; sparse non-vanishing definition and theorem, lines 285–330. The family-dependence issue is not used as a substitute for checking these quantitative hypotheses.

`Submission/Spec.lean` retains its original two `sorry`s and its original SHA-256:

```
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```

**Conclusion:** bias-centering genuinely exposes a difference of multiplicative functions, and the centered local Liouville phase genuinely has the extra `p^(-1)` saving in (23). The unfinished step is promoting this local calculation to an estimate for the explicit arithmetic cofactor remainder (25), with enough control to retain the top `h`-shift and its common prime-free anchor. Neither that step nor the equivalent conditional balance (35) has been proved. The failed uniform-norm approach is not being used to rule out such a phase-specific estimate, and no proof or disproof of Erdős #5 is claimed.
