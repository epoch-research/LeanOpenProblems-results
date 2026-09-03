# Erdős 371: an exact reflection reduction and its remaining obstruction

## Status and formal specification

This note does **not** prove or disprove the natural-density conjecture. It isolates a precise signed estimate, proves several all-scale reductions, and identifies why replacing that estimate by an absolute-value bound fails. Full independence is not assumed.

`Submission/Spec.lean` is unchanged. Its target is

```lean
{ n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n }.HasDensity (1/2)
```

Here `Nat.maxPrimeFac` is genuinely the greatest prime divisor, with values 0 at 0 and 1 at 1 (`FormalConjecturesForMathlib/Data/Nat/MaxPrimeFac.lean:25–28`). `Set.HasDensity` is ordinary natural density, the limit of the count in `[0,N)` divided by `N`, and the target `1/2` is real (`Data/Set/Density.lean:42–44,83–93`). Neither admitted declaration in `Spec.lean`, including its `disproof` stub, is used.

`Submission/ReflectionFacts.lean` independently proves: no ties between consecutive largest prime factors; downward ordering is the complement of upward ordering; the single-cutoff telescoping identity; the exact signed-count identity; the adjacent-cutoff bin identity; and an equivalence between the exact Lean target and vanishing of its ordinary signed counting average (`erdos371_iff_signedMean`). These are partial formal results, not a formal proof of the analytic reductions below or of Erdős 371.

## Corpus inputs, with exact locations

1. Joni Teräväinen, *On binary correlations of multiplicative functions*, arXiv:1710.01195, Forum Math. Sigma 6 (2018), e10.
   - `binary_correlations_arxiv2.tex:54–58`, label `theo_bincorr`: a logarithmic correlation theorem over `[x/omega(x),x]`, for every arbitrarily slowly growing `omega`.
   - Lines 134–159, labels `theo_density`, `theo_erdos`: logarithmic smooth-pair independence and logarithmic ordering density 1/2.
   - Lines 177–184, label `theo_hildebrand`: **positive asymptotic lower density** for every nonempty exponent box for `(P(n),P(n+1))`. This stronger-than-log-positivity fact is useful below.
   - Lines 83–87 explicitly explain why fixed-function pretentious correlation asymptotics cannot be used uniformly for moving smooth cutoffs.
2. Terence Tao and Joni Teräväinen, *The structure of correlations of multiplicative functions at almost all scales*, arXiv:1809.02518, Algebra & Number Theory 13 (2019), 2103–2150.
   - `1809.02518.tex:213–219`, label `cor1`: density 1/2 outside an exceptional set of scales of logarithmic density zero.
   - Lines 242–258, label `isotopy`: the reflection/isotopy result also has exceptional scales.
   - Lines 1077–1083, label `rem1`: the adaptation to moving smooth cutoffs and almost-all-scale smooth-pair independence.
   - Lines 176–178 explain the gap between logarithmic-density-zero and natural-density-zero exceptional scales.
3. Yanan Jiang and Steven J. Miller, *Generalizing Ruth-Aaron Numbers*, arXiv:2010.14990.
   - `2010.14990.tex:398–403`, label `thm:xdeltapn`:
     for every epsilon > 0 there are delta > 0 and X0 such that, for **every** X >= X0,
     `#{n <= X: X^(-delta) < P(n)/P(n+1) < X^delta} < epsilon X`.
   - Lines 405–492 give the small-prime CRT and large-prime/cofactor upper-sieve argument. Thus the diagonal issue is already controlled at all scales.

## 1. Adjacent cutoffs suffice; an aggregate condition is equivalent

Let N >= 2 be an integer. Work with `1 <= n < N`, so both integers in each pair are at most N. This differs from the Lean counting interval by one term only. Define

\[
g_t(n)=1_{P(n)\le N^t},\quad
S_{a,b}(N)=\sum_{1\le n<N}g_a(n)g_b(n+1),\quad
D_{a,b}=S_{a,b}-S_{b,a}.
\]

Also let

\[
I(N)=\sum_{1\le n<N}\operatorname{sgn}(P(n+1)-P(n))
     =2A(N)-(N-1).
\]

There are no ties: a common greatest prime factor would divide both consecutive integers, hence 1. The endpoint conventions cause no ties either.

For an integer K >= 2, bin `log P(n)/log N` in K consecutive intervals of width 1/K, with 0 included in the first bin. If r,s are the two bin labels, then exactly

\[
\operatorname{sgn}(s-r)=
\sum_{j=1}^{K-1}
\left(1_{r\le j}1_{s\le j+1}
      -1_{s\le j}1_{r\le j+1}\right).
\tag{1}
\]

For r<s, the only nonzero summand is j=s-1. The r>s case is its negative. This identity is also kernel-checked in `adjacent_cutoff_bins`.

Consequently, with

\[
E_K(N)=\#\{1\le n<N:
 |\log P(n+1)-\log P(n)|\le (\log N)/K\},
\]

we have the finite inequality

\[
\left|I(N)-\sum_{j=1}^{K-2}D_{j/K,(j+1)/K}(N)\right|
\le E_K(N)+1.
\tag{2}
\]

The omitted last summand is `D_{(K-1)/K,1}=g_{(K-1)/K}(1)-g_{(K-1)/K}(N)`, of absolute value at most 1. Same-bin pairs account for the entire remaining error.

The Jiang–Miller lemma implies

\[
\eta_K:=\limsup_{N\to\infty}E_K(N)/N\longrightarrow0.
\tag{3}
\]

Use a slightly larger delta than 1/K to avoid any issue about strict inequalities in that lemma.

Thus proving `D_{a,b}(N)=o(N)` for fixed rational `0<a<b<1` suffices, with no independence and no uniformity in a,b required. In fact the strictly weaker criterion

\[
\boxed{
\lim_{K\to\infty}\limsup_{N\to\infty}
\frac1N\left|\sum_{j=1}^{K-2}D_{j/K,(j+1)/K}(N)\right|=0
}
\tag{4}
\]

is **equivalent** to the actual density conjecture, using (2)–(3). This permits cancellation between different cutoff currents. The order of limits is essential: first fix K, then let N tend to infinity.

Changing cutoffs from `n^a` to `N^a` costs o(N) unconditionally. For example, discard `n < N^(1-epsilon)` and bound the remaining discrepancy by a one-variable smooth-number count in the exponent interval `[a(1-epsilon),a]`; then use continuity of `F(a)=rho(1/a)` and let epsilon decrease to zero.

## 2. What one-cutoff balance proves, and what it does not

For every threshold, even one depending on N,

\[
\sum_{1\le n<N}
\bigl(g(n)(1-g(n+1))-(1-g(n))g(n+1)\bigr)=g(1)-g(N).
\tag{5}
\]

So upward and downward crossings of any **single** threshold balance exactly up to endpoints.

For two nested cutoffs, put `L=g_a`, `M=g_b-g_a`, `H=1-g_b`. Then D_ab is the net transition current L->M minus M->L. By telescoping row minus column counts, this agrees up to endpoints with the currents M->H minus H->M and H->L minus L->H. The missing information is a three-state circulation, not a marginal distribution.

For example, let U be uniform on [0,1], Q be the inverse CDF of the Dickman exponent law, and set

\[
(U_1,U_2)=(Q(U),Q((U+1/3)\bmod1)).
\]

Both marginals have exactly the Dickman law. This coupling is separated from the diagonal by a positive distance, but `Pr(U_2>U_1)=2/3`. This is not an arithmetic counterexample; it shows rigorously that equal marginals plus near-diagonal nonconcentration do not entail reflection symmetry.

## 3. Exact inclusion–exclusion and CRT reflection

Write `y=N^a`, `z=N^b`, and let

\[
\mathcal R_y=\{d\le N:\mu(d)\ne0,\ P^-(d)>y\},
\]

including d=1 by the convention `P^-(1)=infinity`. Then for every positive m<=N,

\[
g_a(m)=\sum_{d\mid m,\ d\in\mathcal R_y}\mu(d).
\]

Let

\[
C_N(d,e)=\#\{1\le n<N:d\mid n,\ e\mid n+1\},\qquad
R_N(d,e)=C_N(d,e)-C_N(e,d).
\]

Terms with `(d,e)>1` are zero. For coprime d,e, put q=de and let `0<=r<q` satisfy `r=0 (mod d)`, `r=-1 (mod e)`. The reflected residue is exactly `q-1-r`. With `t=(N-1) mod q`,

\[
R_N(d,e)=1_{0<r\le t}-1_{0<q-1-r\le t},\qquad |R_N(d,e)|\le1.
\tag{6}
\]

The full-period contributions cancel **exactly**, not asymptotically. Therefore

\[
D_{a,b}=
\sum_{d\in\mathcal R_y,e\in\mathcal R_z\atop(d,e)=1}
\mu(d)\mu(e)R_N(d,e).
\]

The part with both d,e in `R_z` cancels by swapping them. The terms e=1 give exactly `1_{y<P(N)<=z}`. Hence

\[
D_{a,b}=1_{y<P(N)\le z}+
\sum_{d\in\mathcal R_y\setminus\mathcal R_z,\ e\in\mathcal R_z\setminus\{1\}
\atop(d,e)=1}\mu(d)\mu(e)R_N(d,e).
\tag{7}
\]

Only a d with a prime factor in (y,z] remains; the common-high-prime part has already disappeared.

## 4. An unconditional all-scale cancellation range

For `N <= Q <= N log N`, the portion of (7) with `de<=Q` is

\[
O_a(Q/\log N).
\tag{8}
\]

Proof: q=de is squarefree and every prime factor exceeds N^a. Also `omega(q)<=2/a` for N large. There are at most `2^{omega(q)}` assignments of its primes to d,e. The number of such rough squarefree q<=Q is `O_a(Q/log N)`. One elementary proof chooses a prime factor p and writes q=mp, applies `pi(Q/m) << Q/(m log y)`, and bounds

\[
\sum_{m\text{ squarefree, rough}}1/m
\le\prod_{y<p\le Q}(1+1/p)\ll\log Q/\log y=O_a(1).
\]

Now apply (6). In particular, put `Q_N=N sqrt(log N)` and define T_ab(N) to be the sum in (7) restricted to `de>Q_N`. Then

\[
\boxed{D_{a,b}(N)=T_{a,b}(N)+O_a(N/\sqrt{\log N}).}
\tag{9}
\]

The bounded boundary term is absorbed. All subcritical moduli, and even this mildly superlinear range, are harmless.

For the remaining terms d,e>1 let `v=bar d_e` be the inverse of d modulo e in `{1,...,e-1}`. Since de>N, (6) becomes

\[
R_N(d,e)=1_{d(e-v)\le N-1}-1_{dv\le N}.
\tag{10}
\]

Thus the precise remaining task is a **signed endpoint discrepancy for modular inverses**, weighted by `mu(d)mu(e)` on two different rough supports. Ordinary local CRT densities have already canceled.

Combining (2) and (9), criterion (4) remains equivalent to Erdős 371 with every D replaced by T. This is a single explicit residual criterion, weaker than separate reflection limits and much weaker than full independence.

## 5. The surviving tail has linear absolute mass

For every fixed `0<a<b<1`,

\[
\sum_{d\in\mathcal R_y\setminus\mathcal R_z,\ e\in\mathcal R_z\setminus\{1\}
\atop(d,e)=1,\ de>Q_N}|R_N(d,e)|\asymp_{a,b}N.
\tag{11}
\]

The upper bound is immediate: each n<=N has at most `2^{1/a}` squarefree divisors with all primes>N^a, and similarly at the other threshold; use `|R|<=C(d,e)+C(e,d)`.

For the lower bound, choose fixed exponents

\[
a<u_0<u_1<b<v_0<v_1<1,\qquad u_0+v_0>1.
\]

Such a choice is possible for every a<b. Teräväinen's positive-lower-density box theorem gives at least cN integers in the corresponding box for `(P(n),P(n+1))`, for all large N. After removing `n<cN/2`, there are still at least cN/2. For these integers,

- `p=P(n)` is in `(N^a,N^b]`;
- `q=P(n+1)>N^b`;
- `pq>Q_N` and in fact `pq>2N` for all large N.

Every pair (p,q) supplies a prime-prime term of (7), of weight +1. Its CRT solution is unique below N; its reflected solution cannot also be below N since the two residues sum to pq-1>2N-1. Distinct n therefore give distinct terms with `R_N(p,q)=+1`. The reversed exponent box similarly gives linearly many terms with value -1. Both boxes lie a fixed positive distance from the diagonal.

Thus the obstruction is not merely a crude error estimate: even after common-support cancellation, the remaining unsigned mass really is linear. It cannot be made o(N) by discarding near-diagonal pairs or by bounding every term absolutely. Some genuine signed cancellation is indispensable. There is also a uniform mesh version of this obstruction: use fixed boxes, say with prime-factor exponents in `(0.60,0.65)` and `(0.85,0.90)`. For every sufficiently fine mesh, each such prime pair belongs to one surviving adjacent-cutoff tail with lower cutoff greater than 1/2. The sum of the termwise absolute masses over the mesh is therefore at least cN with c independent of the mesh size.

## 6. A further slice cancels by Bombieri–Vinogradov

There is an additional, standard-prime-distribution partial result, without prime-pair asymptotics.

Assume `b>1/2`, so every nontrivial e in `R_z` is a prime. Put

\[
\mathcal M=\mathcal R_y\setminus\mathcal R_z,\quad
K_0=\lfloor N/z\rfloor,\quad x_k=N/k.
\]

For `(k,d)=1`, let

\[
B_k(d)=
 [\pi(x_k;d,\bar k)-\pi(z;d,\bar k)]
 -[\pi(x_k;d,-\bar k)-\pi(z;d,-\bar k)].
\]

Regrouping by the complementary factor k gives

\[
D_{a,b}(N)=
-\sum_{k\le K_0}\sum_{d\in\mathcal M\atop(d,k)=1}\mu(d)B_k(d)+O_a(1).
\tag{12}
\]

Here the two equations are `kq-1=dm` and `kq+1=dm`; the minus sign in (12) is `mu(q)=-1`. Making their upper endpoints identical changes only `kq=N`; there is at most one prime q>sqrt(N) dividing N, and at most O_a(1) relevant rough divisors of N+1. This explains the endpoint error.

The usual maximal-in-endpoint Bombieri–Vinogradov theorem implies: for every A>0 one can choose B such that the part of (12) with

\[
d\le \sqrt{x_k}/(\log N)^B
\tag{13}
\]

is `O_{A,a,b}(N/(log N)^A)`. Indeed, the two main terms `li(.)/phi(d)` cancel; apply the maximum-over-residue-class estimate for each k and sum errors `<< (N/k)/(log(N/k))^(A+2)`. Since `x_k>=N^b`, the harmonic k-sum is harmless.

This gives real all-scale **sieve cancellation**, not an invocation of independence. But it leaves the complementary long-modulus range in (12). In the particularly clean case `a>1/2`, every d in M is already a prime greater than sqrt(N), so none lies in (13). Divisor switching in that remaining range reintroduces the second primality condition; it does not turn the problem into a one-prime progression estimate.

## 7. The clean double-prime obstruction

For `1/2<a<b<1`, inclusion–exclusion terminates after the first prime on each side. Formula (7) is exactly

\[
D_{a,b}(N)=O(1)+
\sum_{N^a<p\le N^b,\ N^b<q\le N}
\bigl(C_N(p,q)-C_N(q,p)\bigr).
\tag{14}
\]

Equivalently, after setting `n=mp`, `n+1=kq`, the required signed estimate is the average over

\[
m\le N^{1-a},\qquad k\le N^{1-b}
\]

of the difference between the counts of prime p,q in the indicated ranges satisfying

\[
kq-mp=+1\quad\text{and}\quad kq-mp=-1,
\qquad mp,kq\le N.
\tag{15}
\]

For each fixed m,k, the local root counts and putative singular series for the two signs agree by reflection. However:

- full CRT periods are much longer than the interval;
- the usual one-prime Bombieri–Vinogradov range misses this regime;
- upper-bound sieve estimates for both signs give O(N)-scale bounds after summation, not o(N) for their difference;
- reciprocity swaps the relevant inverse fractions but does not interchange the different cutoff supports.

It is **not necessary** to prove an asymptotic for either prime-pair count separately. The signed average in (15) is a weaker target. Nothing above proves it, and equality of local factors is not such a proof.

## 8. Why the two tempting limit passages fail

### Finite-prime reflection

For a fixed finite set of primes, divisibility patterns have a finite period and reflection is exact over complete periods. But the required cutoffs move with N. Truncating the excluded primes at a fixed Z gives the constant function 1 once N^a>Z, whereas the true smooth indicator has mean `rho(1/a)<1`. There is no uniform L1 approximation. The full prime-divisibility model through Z has primorial period `exp((1+o(1))Z)`, so taking Z>=N^a is far beyond the short-period regime. Sparsely truncating the forbidden-prime interval instead would require a separate approximation estimate, not supplied by periodic symmetry. Formula (9) states exactly a portion for which a uniform argument *is* valid.

### Exceptional scales

Logarithmic density and almost-all scales do not entail natural density, even with ordinary scale continuity. For example, start with the even integers and add all integers in `[N_j,2N_j)`, with `N_j=2^(2^j)`. The resulting set has logarithmic density 1/2 and has ordinary partial density tending to 1/2 outside a logarithmic-density-zero set of scales (one may exclude `[N_j,jN_j]`). Yet its partial density tends to 3/4 along `2N_j`. For each fixed error tolerance, the bad scale set even has logarithmic Banach density zero. This is not an arithmetic counterexample; it rules out that Tauberian inference without new arithmetic information.

## Optional quantitative form of the diagonal error

The same two-case proof as Jiang–Miller gives the useful bound

\[
\limsup_N N^{-1}\#\{n<N:|\log P(n+1)-\log P(n)|\le\delta\log N\}
\ll\delta^{1/3}
\]

for small fixed delta. This is a deduction from the proof, not the quoted statement of their lemma. To see it, remove `P(n)<N^eta` and the band `N^(1/2-eta)<=P(n)<=N^(1/2+eta)`, of upper density O(eta). The small-prime case contributes `O(delta/eta)` by CRT and prime reciprocal sums. In the large-prime case the cofactors have product at most `2N^(1-2eta+delta)` and ratio in `[N^(-delta)/2,2N^delta]`. The uniform two-linear-form upper sieve and `sum_{m<=T}1/phi(m)=C log T+O(1)` bound that case by `O(delta/eta^2)` in upper density. Set eta=delta^(1/3). Only an upper-bound sieve is needed here, unlike the off-diagonal signed problem.

## Verification and remaining requirement

- The finite mesh identity was checked algebraically and by exact integer computations (`P(n)^K<=N^j`, not floating-point thresholds), for N<=299 and K<=17.
- Inclusion–exclusion, CRT reflection, symmetric-support removal, and the boundary term in (7) were independently checked for 297 test cases with N<=300.
- The cofactor/prime-progression regrouping (including `mu(q)=-1` and the endpoint correction in (12)) was checked for 391 cases with N<=400.
- `lake env lean Submission/ReflectionFacts.lean` succeeds. All eight displayed proved declarations, including the equivalence for the exact target, use only `propext`, `Classical.choice`, and `Quot.sound`, not `sorryAx`.
- The initial and final SHA-256 of `Submission/Spec.lean` is `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.

The unresolved requirement is a proof that the signed large-modulus sum T_ab defined in (9)–(10) is o(N), or merely that its adjacent-mesh aggregate in (4), with D replaced by T, tends to zero. Proving that aggregate would yield the exact Lean conjecture; this analytic cancellation estimate and its formalization are not supplied here. There is no valid proof or disproof of Erdős 371 in this work.
