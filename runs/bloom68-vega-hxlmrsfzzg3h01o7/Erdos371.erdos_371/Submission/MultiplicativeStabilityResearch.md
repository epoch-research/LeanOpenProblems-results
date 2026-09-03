# Erdős 371: multiplicative stability, dilation, and a resonant countermodel

## Status and scope

This is a mathematical research note, not a proof or disproof of Erdős 371. No Lean file has been edited. In particular, neither admitted declaration in `Submission/Spec.lean` is used. The conjecture was genuinely open in the requested 2022 timeframe.

The main conclusions are:

1. **Same-scale strong stationarity would suffice**, but weak multiplicative stability does not give it.
2. There is an **exact doubling reduction**, with no analytic error if one uses raw largest prime factors. The missing estimate is an explicitly signed bypass count.
3. **Dyadic flatness plus logarithmic Banach density zero of bad scales really does imply the desired all-scale limit.**
4. The abstract hypotheses suggested in the question are insufficient: one can construct a bounded deterministic sequence with uniform fixed-multiplier stability, the Dickman marginal at every scale, all-scale near-diagonal nonconcentration, and logarithmic-Banach-density-zero bad *ascent* scales, but with a nonvanishing dyadic difference. A construction and its verification are given below.
5. A further valid conditional route uses **nearby large dilations and known short-interval uniformity**. It reduces the problem to an explicit antisymmetric residue-decoupling estimate, without assuming dyadic flatness or full pair independence. That new estimate is not proved here.

The counterexample is **not** a counterexample to the prime-factor conjecture. It does not reproduce all known information about smooth numbers: in particular, it is not claimed to have almost-all-scale *joint smooth-pair independence* or all-scale uniform short-interval marginals. It addresses precisely the proposed qualitative stability/marginal/nonconcentration/ascent-bad-scale inference. It also does not reproduce the quantitative bound (1) or the full identity `P(ab)=max(P(a),P(b))` for variable multipliers.

## 1. Definitions and existing inputs

The Lean target is

```lean
{ n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n }.HasDensity (1/2)
```

`Nat.maxPrimeFac` is the greatest prime divisor, with `P(0)=0`, `P(1)=1`. `Set.HasDensity` is ordinary natural density, with real target `1/2`. The extra `disproof` declaration in the specification is an admitted stub, not mathematical evidence.

Set

\[
s_n=\operatorname{sgn}(P(n+1)-P(n)),\quad
D(N)=\sum_{1\le n\le N}s_n,\quad a(N)=D(N)/N.
\]

Consecutive largest prime factors cannot be equal, since a common prime would divide 1. Consequently the target is exactly `a(N) -> 0`, up to the harmless choice of counting endpoints.

For `n>=2`, put

\[
f(n)=\frac{\log P(n)}{\log n}.
\]

For every `k>=1`,

\[
|f(kn)-f(n)|\le \frac{\log k}{\log(kn)}. \tag{1}
\]

Indeed, write `L=log n`, `c=log k`, and `log P(kn)=log P(n)+d`, where `0<=d<=c`. The difference is `(d-c f(n))/(L+c)`.

There is an additional useful simplification: **the signs of the normalized and raw ascents agree for every `n>=3`**. The sole tie introduced by normalization at `n>=2` is `f(2)=f(3)=1`. To prove this, if `p=P(n+1)>q=P(n)`, then

\[
\log p-\log q\ge\log(1+1/q)\ge\log(1+1/n)
\ge f(n)\log(1+1/n).
\]

Equality throughout requires `q=n` and `p=q+1`, hence the consecutive primes 2 and 3. If `p<q`, the normalized inequality is plainly strict in the other direction.

The one-variable exponent distribution is

\[
F(u)=\rho(1/u),\quad 0<u\le1,\qquad F(0)=0,
\]

where `rho` is the Dickman function. `F` is a continuous strictly increasing CDF on `[0,1]`; write `Q=F^{-1}`.

Inputs checked in the local corpus:

- Teräväinen, *On binary correlations of multiplicative functions*, arXiv:1710.01195, `theo_density`, `theo_erdos`: logarithmic smooth-pair independence and logarithmic ascent density `1/2`.
- Tao–Teräväinen, *The structure of correlations of multiplicative functions at almost all scales*, arXiv:1809.02518, `cor1`, `rem1`: the corresponding almost-all-scale result. The fixed-error logarithmic Banach formulation follows from the argument of Corollary `elliott-1(i)`/Remark `18-rem` applied as in `rem1`; this is stronger than merely saying there is one exceptional set of logarithmic density zero.
- Jiang–Miller, *Generalizing Ruth-Aaron Numbers*, arXiv:2010.14990, lemma `thm:xdeltapn`: for every epsilon there is delta such that, for all sufficiently large `X`, fewer than `epsilon X` integers `n<=X` satisfy `X^{-delta}<P(n)/P(n+1)<X^delta`. In particular

\[
\lim_{\delta\downarrow0}\limsup_{X\to\infty}
\frac1X\#\{n\le X:|f(n+1)-f(n)|\le\delta\}=0. \tag{2}
\]

For the last implication discard `n<epsilon X`, compare `log n` with `log X`, and then let epsilon decrease.

## 2. What stationarity and dilation do — and do not — prove

### 2.1 A valid sufficiency theorem

Let `(Z_h)_{h in Z}` be a stationary real-valued process. Suppose

\[
(Z_0,Z_k)\overset d=(Z_0,Z_1)\qquad(k=1,2,\ldots). \tag{3}
\]

Then its pair law is exchangeable. For bounded real functions `phi,psi`, the left side of

\[
\mathbb E\phi(Z_0)\psi(Z_1)
=\frac1H\sum_{k=1}^H\mathbb E\phi(Z_0)\psi(Z_k)
\longrightarrow
\mathbb E\big[\mathbb E(\phi(Z_0)\mid\mathcal I)
              \mathbb E(\psi(Z_0)\mid\mathcal I)\big]
\]

is independent of `H`; the limit is symmetric in `phi,psi`, by the mean ergodic theorem. Product tests determine the pair law. No ergodicity assumption is needed. In fact the pair law is a mixture of product laws. Nonconcentration is needed only when passing to the discontinuous ordering statistic.

It would even suffice to have (3) just for the antisymmetric product tests. This is a valid conditional proof route, not a consequence of (1).

### 2.2 The actual dilation identity

Let `mu_X` denote empirical window laws with base point uniform in `[1,X]`. Multiplicative stability gives

\[
\mathbb E_{n\le X}\Phi(f(n),f(n+1))
=
\mathbb E_{\substack{m\le kX\\m\equiv0\pmod k}}
\Phi(f(m),f(m+k))+o(1) \tag{4}
\]

for continuous `Phi` (and suitable ordering tests using (2)). The conditional average on the right is normalized by its own sample size.

There are **two distinct gaps** between (4) and (3):

- removing the residue condition is a two-point equidistribution assertion, not a consequence of equality of one-variable marginals;
- even if that condition can be removed, the scale changes from `X` to `kX`.

Stationarity of a subsequential window law is automatic from shifting the counting interval by `O(1)`. It does not remove either gap. Taking an invariant average over multiplicative scales can restore a symmetry while losing a bad individual scale — exactly the distinction relevant here.

## 3. Exact doubling and the missing signed bypass estimate

For distinct real `x,z,y`,

\[
\operatorname{sgn}(z-x)+\operatorname{sgn}(y-z)
=2\operatorname{sgn}(y-x)\,1_{\min(x,y)<z<\max(x,y)}. \tag{5}
\]

For prime factors this can be used **without normalized-exponent errors**: `P(2n)=P(n)` for every `n>=2`. Also `P(2n+1)` is distinct from both `P(n)` and `P(n+1)`, by the same coprimality argument. Put

\[
B_n=1_{\min(P(n),P(n+1))<P(2n+1)<\max(P(n),P(n+1))}.
\]

Then (5) gives `s_{2n}+s_{2n+1}=2s_n B_n` for `n>=2`; it also happens to hold for `n=1`. Thus, with the definitions above,

\[
D(2N)=2\sum_{n\le N}s_nB_n+s_1-s_{2N+1}, \tag{6}
\]

and therefore

\[
\boxed{a(2N)-a(N)=-\frac1N\sum_{n\le N}s_n(1-B_n)+O(1/N).} \tag{7}
\]

The exact new target is cancellation of the **signed bypass current** on triples whose intermediate value lies outside the two endpoints. In the order `(x,z,y)=(P(n),P(2n+1),P(n+1))`, it is

\[
\Pr(x<y<z)+\Pr(z<x<y)-\Pr(y<x<z)-\Pr(z<y<x).
\]

Marginal balance and near-diagonal nonconcentration do not bound this signed quantity. The four order patterns can all be uniformly separated from ties.

For a simple local test, take a uniform `U` and

\[
x=Q(U),\quad y=Q(\{U+1/3\}),\quad z=Q(\{U+2/3\}).
\]

All three marginals are `F` and the pairs stay away from the diagonal. The coarse current is `1/3`, the mean fine-edge current is `-1/3`, and the bypass current is `2/3`. Conversely, inserting `Q({U+1/6})` between `Q(U)` and `Q({U+1/3})` increases the mean current from `1/3` to `2/3`. Thus there is no general contraction or monotonicity of the absolute current under refinement.

## 4. Dyadic flatness is genuinely sufficient with Banach-zero bad scales

Here is the exact Tauberian statement used in the proposed route.

**Lemma.** Let `a(N)=N^{-1} sum_{n<=N} s_n`, `|s_n|<=1`. Suppose for every epsilon>0 the set

\[
E_\epsilon=\{N:|a(N)|>\epsilon\}
\]

has logarithmic Banach density zero. If `a(2N)-a(N)->0`, then `a(N)->0`.

**Proof.** Linearly interpolate the partial sums and set `b(t)=a(e^t)`. This changes integer averages by `O(1/N)` and makes `b` 2-Lipschitz, since `b'=s-a` almost everywhere. Write `L=log 2`. If `|b(t_j)|>=epsilon` arbitrarily far out, then for any fixed integer `M`, dyadic flatness makes

\[
|b(t_j+rL)-b(t_j)|\le\epsilon/4\qquad(0\le r\le M)
\]

once `t_j` is large enough. Lipschitz continuity then supplies intervals of a fixed positive length `delta=delta(epsilon)<L/2`, around all these grid points, on which `|b|>epsilon/2`. Their proportion in an interval of length about `ML` is bounded below independently of `M`. Taking arbitrarily large `M` contradicts upper Banach density zero in logarithmic coordinates. Integer and interpolated bad sets agree up to harmless changes of tolerance. QED.

Ordinary logarithmic density zero would not suffice: increasingly wide but increasingly isolated humps in `log N` give a counterexample. The fixed-error Banach formulation is essential.

Combining the known bad-scale input with (7), the following is a valid proof route:

\[
\boxed{\sum_{n\le N}s_n(1-B_n)=o(N).} \tag{8}
\]

Nothing in this note establishes (8) for prime factors.

## 5. A stronger obstruction: an actual stable deterministic countersequence

This section proves that the proposed abstract qualitative hypotheses do not force (8), dyadic flatness, or zero orientation current.

### 5.1 Statement

For every continuous strictly increasing CDF `F` on `[0,1]`, there exists a deterministic sequence `g:N->[0,1]` such that:

1. For every fixed positive integer `k`,
   `sup_{n>=M}|g(kn)-g(n)| -> 0` as `M->infinity`.
2. At every scale, `N^{-1}#{n<=N:g(n)<=u}->F(u)` for every `u`.
3. `lim_{delta->0} limsup_N N^{-1}#{n<=N:|g(n+1)-g(n)|<=delta}=0`.
4. If `a_g(N)=N^{-1} sum_{n<=N} sgn(g(n+1)-g(n))`, then for every epsilon>0 the set `{N:|a_g(N)|>epsilon}` has logarithmic Banach density zero.
5. Nevertheless, along a sequence `N_j->infinity`,
   `a_g(2N_j)-a_g(N_j)>0.24` eventually, and along another such sequence `a_g(N)>0.36` eventually.

Thus it has the logarithmic/ascent-almost-all-scale conclusion but not the natural ascent density `1/2`. Its empirical limit processes are stationary, as is true for any bounded sequence.

### 5.2 The resonant phase and the small-prime core

Fix

\[
\eta=1/100,\qquad \beta=1/1000.
\]

Let `h=h_beta:T->[0,1]` be the continuous asymmetric tent map

\[
h(u)=\begin{cases}u/(1-\beta)&0\le u\le1-\beta,\\
(1-u)/\beta&1-\beta\le u<1.
\end{cases}
\]

It is periodic, Lipschitz, and sends Haar measure to the uniform distribution on `[0,1]`.

Let `R_j(n)` be the integer obtained from `n` by deleting all prime factors `<=j`. For every allowed core `r`, choose independent random variables

\[
W_{j,r}\sim\operatorname{Unif}[-\eta/2,\eta/2].
\]

Different `j` also use independent labels. For fixed `k<=j`, `R_j(kn)=R_j(n)` **exactly**.

Choose positive frequencies `tau_j`, growing sufficiently rapidly, with

\[
\|\tau_j\log k\|_{\mathbb R/\mathbb Z}<j^{-2}\quad(1\le k\le j),
\qquad \tau_j>\tau_{j-1}^{20}. \tag{9}
\]

Homogeneous simultaneous Diophantine approximation provides arbitrarily large such frequencies; they can even be chosen as integers. Increase them further to meet the finitely many concentration and smooth-number thresholds below. Set

\[
V_j(n)=h(\{\tau_j\log n+W_{j,R_j(n)}\}). \tag{10}
\]

For fixed `k` and large `j`, `|V_j(kn)-V_j(n)|<=Lip(h)j^{-2}`. The small-prime-core labels supply genuine adjacent randomness without destroying this invariance.

### 5.3 Patching the phases without losing the marginal law

Transition from phase `j-1` to phase `j` on

\[
[\tau_j^{3/5},\tau_j^{4/5}],
\]

using a weight `w(n)` linear in `log n`, from 0 to 1. Outside transition intervals use the sole current phase. These intervals are disjoint by (9).

On a transition put

\[
S(n)=(1-w(n))V_{j-1}(n)+w(n)V_j(n).
\]

Let `H_w` be the CDF of `(1-w)U+wV` for independent uniform `U,V`; let `H_0=H_1` be the identity. Define

\[
G(n)=H_{w(n)}(S(n)),\qquad g(n)=Q(G(n)). \tag{11}
\]

On pure phases this means `G=V_j`. The probability-integral transform in (11) is important: a bare convex combination would not preserve the prescribed marginal.

Useful uniform facts about `H_w`:

- its density is at most 2;
- it is continuous in `(w,s)`;
- for `0<=s<s+ell<=1`,
  `H_w(s+ell)-H_w(s)>=ell^2`, since the event `U,V in [s,s+ell]` suffices;
- consequently every `H_w^{-1}` has the common modulus `|H_w^{-1}(x)-H_w^{-1}(y)|<=sqrt(|x-y|)`.

Weights change by `O_k(1/log tau_j)` under `n->kn`. Combining this with (9), the continuity of the CDF transform, and uniform continuity of `Q` proves assertion 1, for every choice of the random labels. At a transition endpoint a disappearing weight tends to zero, so there is no boundary exception.

### 5.4 Oscillatory estimates needed for the all-scale marginal

On `n asymp N`, the second derivative test gives, for fixed nonzero Fourier coefficients,

\[
\frac1N\sum_{n\asymp N}e(T\log n)
\ll \frac{\sqrt{|T|}}N+\frac1{\sqrt{|T|}}. \tag{12}
\]

Here `e(x)=exp(2 pi i x)`. Throughout phase `j` and its entry transition, `tau_j=o(N^2)`; every nonzero fixed Fourier combination of active frequencies tends to infinity. Rapid separation ensures it is dominated by its largest nonzero frequency. Thus the one or two active phases are jointly Haar-distributed on each fixed-ratio interval, uniformly along arbitrary sequences of scales tending to infinity.

The weights can be frozen on `[cN,N]`, for fixed `c>0`, at an `o(1)` cost. Averaging first over the labels and then using (12), the active `V` values have the law of independent uniforms. Formula (11) therefore gives the uniform marginal for `G`; composition with `Q` gives `F`. Discarding `[1,cN]` and then letting `c` decrease proves the all-scale expected marginal.

### 5.5 Why the random construction has a deterministic realization

For fixed `j`, the number of collisions of cores satisfies

\[
\#\{n,m\le N:R_j(n)=R_j(m)\}
\le N\sum_{a,b\ j\text{-smooth}}\frac1{\max(a,b)}
\le C_jN, \tag{13}
\]

where

\[
C_j=\left(\prod_{p\le j}(1-p^{-1/2})^{-1}\right)^2<\infty.
\]

The first inequality writes `n=ar,m=br`; the second uses `max(a,b)>=sqrt(ab)`.

A bounded statistic of `(g(n),g(n+1))` depends only on the labels of the active phases at `n,n+1`. Statistics at `n,m` are independent unless some labels coincide. Applying (13) to the four possible shifted collisions gives

\[
\operatorname{Var}\left(\sum_{n\le N}\Phi(g(n),g(n+1))\right)
\ll N\sum_{j\le J(N+1)} C_j, \tag{14}
\]

for `|Phi|<=1`; `J(x)` is the largest phase introduced by `x`. The same argument applies to single-site statistics, and to any fixed finite window.

Here is a precise way to arrange the usual diagonal step. On the regime in which `J(N+1)=j`, test the first `j` functions in a countable list containing marginal rational cutoffs, the sign statistic, and rational-width diagonal strips. Use an integer geometric grid of mesh `1+1/j` and tolerance `1/j`. Chebyshev and (14), summed over this grid, have total failure probability

\[
\ll \frac{j^4\sum_{i\le j}C_i}{\tau_j^{3/5}-O(1)}.
\]

Choose `tau_j` so that this is at most `2^{-j}`. Borel–Cantelli and interpolation of bounded partial sums then give, for one realization, empirical average minus its expected average tending to zero **at all scales** for every test in the list. If desired, include fixed finite-window continuous tests in the same list. This is an existence proof of a deterministic `g`, not a claim that the numerical experiments construct its infinite realization.

Also choose `tau_j` so that for all `N>=tau_j^{3/5}-2`, the proportion of `j`-smooth integers up to `N+O(1)` tends to zero with `j`. This is possible because a fixed finite-prime smooth set has density zero. All requirements imposed at stage `j` are finite lower bounds, compatible with (9).

### 5.6 Uniform near-diagonal nonconcentration

At `n+1`, choose an active component with weight at least `1/2`. Except when its core at both `n` and `n+1` is 1, its noise label is independent of all labels used at `n`. Equality of these two cores forces both integers to be `j`-smooth, because consecutive integers are coprime. These exceptions have density `o(1)` by the preceding choice of scales.

Conditioned on the other labels, that component has density at most `1/eta`: a circle interval density bounded by `1/eta` remains so after `h`, since the two inverse-branch lengths sum to 1. Hence `S(n+1)` has conditional density at most `2/eta`.

Let

\[
\omega_F(\delta)=\sup_{|x-y|\le\delta}|F(x)-F(y)|.
\]

Using the inverse modulus of `H_w`,

\[
\limsup_N\frac1N\#\{n\le N:|g(n+1)-g(n)|\le\delta\}
\le \frac{2\sqrt2}{\eta}\sqrt{\omega_F(\delta)}. \tag{15}
\]

Indeed the event forces `G(n+1)` into an interval of length at most `2 omega_F(delta)`, whose inverse image under `H_w` has length at most its square root. The right side tends to zero. The concentration step transfers the expected bound to the chosen realization.

### 5.7 The local limit process and its directed current

At scales `N=t tau_j`, for fixed `t>0`, the entry transition is `o(N)` and the next transition has not begun. The limiting process is

\[
Z_m^{(t)}=Q\big(h(\{U+m/R+W_m\})\big),\qquad m\in\mathbb Z. \tag{16}
\]

Here `h` is the tent map, `R` is uniform on `(0,t)`, `U` is Haar-uniform, and `W_m` are iid uniforms on `[-eta/2,eta/2]`, all independent.

For a direct verification, discard `n<c tau_j`, use

\[
\tau_j\log(n+r)=\tau_j\log n+r/(n/\tau_j)+o(1)
\]

for each fixed integer offset `r`, and apply (12). For `j` larger than all the offsets, distinct adjacent-window cores are distinct unless one is 1: any common factor of `n+r,n+s` divides `r-s` and was deleted. Thus the noise labels in the window are iid, outside a negligible smooth set. Then let `c` decrease.

This process is stationary, conditional on `R`, by translating `U` and reindexing the iid labels. More strongly, its family satisfies exact **cross-scale** dilation consistency:

\[
(Z_{kh}^{(kt)})_{h\in\mathbb Z}\overset d=(Z_h^{(t)})_{h\in\mathbb Z}. \tag{17}
\]

All marginals are `F`, and the diagonal bound is uniform in `t`. Nevertheless (17) is not same-scale invariance (3).

Define the continuous periodic current

\[
J(v)=\mathbb E\operatorname{sgn}\big(h(\{U+v+W_1\})-h(\{U+W_0\})\big).
\]

It has `J(0)=0`, `J(-v)=-J(v)`, and zero period mean. The normalized prefix current has the limit

\[
a_g(\lfloor t\tau_j\rfloor)\longrightarrow
A(t)=\frac1t\int_0^t J(1/r)\,dr. \tag{18}
\]

It follows that `A(t)->0` at both ends: at infinity by `J(0)=0`; at zero by substituting `v=1/r` and integrating a bounded primitive of the mean-zero periodic `J`. Specifically `A(t)=O(t)` as `t->0`.

### 5.8 An explicit certified nonzero dyadic difference

First replace the tent map by the sawtooth `u->{u}` and remove the jitter. Its current is

\[
J_0(v)=1-2\{v\},
\]

away from integers. For `t>1`, direct integration interval by interval gives

\[
A_0(t)=1-\frac{2\log t+2-2\gamma}{t}. \tag{19}
\]

For completeness, the integer tail integral is

\[
\sum_{m=1}^{\infty}\left(\frac1m+\frac1{m+1}-2\log(1+1/m)\right)=2\gamma-1.
\]

Putting back the uniform jitter changes the current only when `v` is within `eta` of an integer. For `1/t>eta`,

\[
|A_{\rm jitter}(t)-A_0(t)|
\le \frac{4\eta\zeta(2)}{t(1-\eta)^2}. \tag{20}
\]

The tent map changes the ordering only if at least one of the two circle values is in its reset interval of measure `beta`. Its effect on a signed current is at most `4 beta`. Hence at `t=4,8`,

\[
|A(t)-A_0(t)|\le\frac{4\eta\zeta(2)}{t(1-\eta)^2}+4\beta.
\]

Therefore

\[
A(8)-A(4)
\ge \frac{\log2+1-\gamma}{4}
 -\frac{4\eta\zeta(2)}{(1-\eta)^2}\left(\frac14+\frac18\right)-8\beta
>0.2458>0.24. \tag{21}
\]

Also `A(8)>0.3620>0.36`. The coarse rigorous bounds `0.577<gamma<0.578`, `0.693<log 2<0.694`, and `zeta(2)<1.645` already certify the strict thresholds `A(8)-A(4)>0.24` and `A(8)>0.36`; the displayed decimals are not needed for the proof. With `N_j=floor(4 tau_j)`, the difference between `2N_j` and `floor(8 tau_j)` is bounded, so (18) and (21) prove assertion 5.

### 5.9 Why bad ascent scales still have logarithmic Banach density zero

Only a bounded multiplicative neighborhood of each resonance `tau_j` can sustain a fixed positive current. Here are the details needed to justify that assertion rather than assume it.

- On a pure phase, if `N/tau_j->infinity`, the two deterministic phases at `n,n+1` differ by `o(1)` for `n asymp N`; the independent jitter then gives an asymptotically exchangeable pair.
- On a pure phase, if `N/tau_j->0`, the two circle phases become jointly Haar-distributed. For Fourier coefficients summing to zero, the additional estimate is

  \[
  N^{-1}\sum_{n\asymp N}e\big(b\tau_j\log(1+1/n)\big)
  \ll \frac{\sqrt{\tau_j}}{N^{3/2}}+\sqrt{\frac N{\tau_j}}=o(1).
  \]

  Pure phase `j` begins after `tau_j^{4/5}`, so the first term is harmless. Coefficients with nonzero sum are handled by (12).
- During the entry transition to phase `j`, the old phase has negligible adjacent increment, while the new pair of phases is jointly Haar and independent of the old single phase. For the Fourier combination

  \[
  m\tau_{j-1}\log n+a\tau_j\log n+b\tau_j\log(n+1),
  \]

  if `a+b!=0`, its second derivative is dominated by `tau_j/N^2`. If `a+b=0,b!=0`, it is dominated by `tau_j/N^3`, since `tau_j/(N tau_{j-1})->infinity` uniformly for `N` in the transition. If `a=b=0`, use the old frequency in (12). All normalized sums tend to zero uniformly on `tau_j^{3/5}<=N<=tau_j^{4/5}`. Freeze the weights on fixed-ratio intervals. The limiting pair of convex combinations is exchangeable, and so is its common CDF transform.

These arguments apply after discarding a lower interval `[1,cN]` and then letting `c` decrease. Nonconcentration justifies the sign tests. A subsequence contradiction now proves: for every epsilon>0 there is a constant `T_epsilon` such that, for all sufficiently large `N`,

\[
|a_g(N)|>\epsilon\quad\Longrightarrow\quad
N\in\bigcup_j[\tau_j/T_\epsilon,T_\epsilon\tau_j]. \tag{22}
\]

The corresponding intervals in `log N` have a fixed length, while the spacings between their centers tend to infinity. Such a union has upper Banach density zero. This proves assertion 4. Partial summation then also gives logarithmic ascent density `1/2`.

This completes the deterministic counterexample construction.

## 6. Farey/Stern–Brocot refinements do not remove the obstruction

For a fixed rational `r=a/b`, the natural value is `f(bn+a)`. Passing to a common denominator is justified by multiplicative stability; for raw `P` it is exact outside a fixed finite-prime smooth set.

If `a/b<c/d` are Farey neighbors, `bc-ad=1`, their two values can be compared after multiplication at

\[
bdn+ad,\qquad bdn+bc=bdn+ad+1.
\]

Thus they do encode a consecutive pair — but **in a residue class and at scale `bdX`**. Inserting the mediant inserts the unrelated additive value

\[
f((b+d)n+(a+c)).
\]

Multiplicative stability supplies no betweenness information about this sum of the two affine forms.

Every insertion adds the triangle defect

\[
\operatorname{sgn}(z-x)+\operatorname{sgn}(y-z)-\operatorname{sgn}(y-x),
\]

which equals `+1` or `-1` for a strict triple, even far from every diagonal. There is no small-mesh bound on its absolute size.

The process model (16) extends consistently to all rational indices by taking iid labels `W_r`, `r in Q`, and using phase `U+r/R`. It is stationary under rational translations and obeys all positive rational cross-scale dilation identities. Hence arbitrary finite rational refinements are available in the same directed model. Positive dilation does not reverse the sign of the drift `1/R`; reflection would. This identifies exactly why generating more Farey identities does not manufacture reflection symmetry.

## 7. A further conditional route: nearby large dilations plus short-interval uniformity

There is a useful way to avoid *assuming* same-scale dilation invariance or dyadic flatness. It uses more than the one-variable global marginal, and isolates the residue-conditioning error alone.

For two centered cutoff functions

\[
u(n)=1_{f(n)\le a}-F(a),\qquad v(n)=1_{f(n)\le b}-F(b),
\]

put

\[
j_q(m)=u(m)v(m+q)-v(m)u(m+q),\qquad
J_q(X)=\frac1X\sum_{m\le X}j_q(m).
\]

Centering changes the uncentered cutoff current only by endpoint terms `O(q/X)`.

The following all-scale short-interval input is available for actual smooth cutoffs:

\[
\epsilon_L(u):=\left(\limsup_{X\to\infty}\mathbb E_{n\le X}
\left|\frac1L\sum_{r=1}^L u(n+r)\right|^2\right)^{1/2}\longrightarrow0, \tag{23}
\]

and likewise for `v`. One location is Tao–Teräväinen, *Value patterns of multiplicative functions and related sequences*, arXiv:1904.05096, definition of uniform distribution in short intervals and the proof of `theo_largest`, lines 1127–1134 of its main source. Its averaged L1 statement implies (23) because the functions are bounded. Moving cutoffs are treated explicitly there.

**Conditional lemma.** Assume (23) and, for every fixed positive integer `q`, the all-scale signed residue-decoupling estimate

\[
\boxed{J_q(qX)-J_1(X)\longrightarrow0.} \tag{24}
\]

Then `J_1(X)->0`.

**Proof.** Fix positive integers `L,H`. For `q=H+r`, `1<=r<=L`, apply (24) at `HX/q`. Ordinary continuity of bounded prefix averages gives

\[
J_{H+r}(HX)=J_1\!\left(\frac{HX}{H+r}\right)+o_X(1)
=J_1(X)+O(L/H)+o_X(1).
\]

Average over `r`. On the other hand,

\[
\frac1L\sum_{r=1}^LJ_{H+r}(HX)
=\mathbb E_{n\le HX}\left[
 u(n)\frac1L\sum_{r=1}^L v(n+H+r)
-v(n)\frac1L\sum_{r=1}^L u(n+H+r)\right].
\]

Cauchy–Schwarz and (23), with the fixed shift `H` removed at an endpoint cost, imply

\[
\limsup_{X\to\infty}|J_1(X)|
\le\epsilon_L(u)+\epsilon_L(v)+O(L/H).
\]

Set `H=L^2` and then let `L` tend to infinity. All integers are fixed before the limit in `X`; there is no unjustified uniformity in a growing modulus. QED.

Multiplicative stability already gives `J_1(X)=E_{n<=X}j_q(qn)+o(1)`. Thus the **unproved** content of (24) is exactly

\[
\frac1{qX}\sum_{m\le qX}(1-q1_{q\mid m})j_q(m)=o(1). \tag{25}
\]

Only antisymmetric currents, not full correlations, need to be decoupled from a residue class. One-variable equidistribution in arithmetic progressions does not prove (25).

The proof permits an even weaker block-averaged version: with `H_L/L->infinity`, it suffices that

\[
\lim_{L\to\infty}\limsup_{X\to\infty}
\left|\frac1L\sum_{r=1}^L
\left[J_{H_L+r}(H_LX)
-J_1\!\left(\frac{H_LX}{H_L+r}\right)\right]\right|=0. \tag{26}
\]

For example one may fix `H_L=L^2`. This is a concrete candidate target for averaged residue decoupling. It exploits the ratios `H_L/(H_L+r)` being close to 1, not an assumed slow variation of correlations under a fixed dilation. Proving (25) or (26) for the actual cutoffs remains open in this analysis.

Applying the conditional lemma to the adjacent cutoff currents in a fine mesh, then using near-diagonal nonconcentration, would prove the ascent density. The finite mesh identity and its endpoint terms are already documented in `ReflectionResearch.md` and checked algebraically in `ReflectionFacts.lean`.

The countersequence in Section 5 does **not** satisfy (23). On scales with `N/tau_j->infinity` before the next phase transition, its pair law tends to

\[
\big(Q(h(U+W_0)),Q(h(U+W_1))\big),
\]

with a common invariant phase `U`. Conditional short-interval means depend nontrivially on `U`. This also explains its failure of the actual almost-all-scale smooth-pair independence theorem. Consequently the counterexample rules out the proposed weak package, not a possible argument using this stronger arithmetic input.

## 8. What remains unproved

Three honest reductions have been isolated:

- **Direct dyadic route:** prove the signed bypass estimate (8). Together with Banach-zero bad ascent scales this proves Erdős 371.
- **Stationary-law route:** establish same-scale invariance of antisymmetric pair tests. The mean ergodic argument then proves reflection.
- **Nearby-large-dilations route:** use the available short-interval estimate (23) and prove only the signed residue-decoupling condition (25), or its weaker block version (26). This avoids assuming dyadic flatness and does not require full pair independence as an input.

None of the three missing signed estimates is established here. The counterexample rigorously shows why qualitative fixed-multiplier stability, an all-scale marginal, stationarity, near-diagonal nonconcentration, and even Banach-zero bad ascent scales cannot by themselves fill the gap. New arithmetic information must enter. There is no claimed completion of the open conjecture.

## Verification record

- `lake env lean Submission/ReflectionFacts.lean` succeeded. All eight listed facts have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom reports, not `sorryAx`. This checks the pre-existing elementary facts, not this analytic note.
- Exhaustively checked (5) on all six strict order types.
- A sieve checked (6) for every `n<=250000`; with `N=250000`, both sides gave `D(500000)=386`.
- The same sieve found only `n=2` as a normalized/raw sign discrepancy, consistent with the proof above.
- The explicit error bound in (21) gives `0.2458078855...`.
- Independent Monte Carlo checks of the model, with two million samples each, gave approximately `A(4)=0.094712`, `A(8)=0.373043`. These are sanity checks only; (19)–(21), not simulation, certify the obstruction.
- `Submission/Spec.lean` SHA-256: `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.
- `Submission/ReflectionFacts.lean` SHA-256: `e0db5e10708791ce7172b31c03a0c6f1442876dfa41b1e5cf24a9aea01578f35`.
