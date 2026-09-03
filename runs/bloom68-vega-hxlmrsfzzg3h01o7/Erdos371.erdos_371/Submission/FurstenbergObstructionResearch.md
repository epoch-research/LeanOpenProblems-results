# Erdős 371: arithmetic and dynamical obstructions to a pair-reversal route

## Outcome and scope

This note does **not** prove natural density `1/2`, and does **not** give a nonreversible natural-prefix limit of the actual largest-prime-factor sequence. It supplies several exact obstructions to proposed routes, rather than restating the missing signed-residue estimate.

The principal new deductions are:

1. **The topological orbit closure of the actual normalized sequence is not uniquely ergodic.** An explicit CRT construction on prime exponents, followed by cyclotomic factorization, produces arbitrarily long blocks on which every normalized largest-prime exponent tends to zero. Thus the closure contains the constant-zero point and its invariant point mass. Every natural-prefix limit, in contrast, has the nondegenerate Dickman marginal. In particular, an exact continuous realization of the sequence in a uniquely ergodic compact system is impossible.
2. **Not all natural-prefix Furstenberg systems can have finite tower rank.** The known almost-all-scale binary theorem permits selection of one natural-prefix limit with independent Dickman coordinates at every distinct pair of times. Its Koopman representation contains countably many orthogonal copies of the bilateral shift, ruling out every finite tower rank. No assertion at a bad scale is used here.
3. A completely consistent **stationary, all-integer-dilation-invariant** probability model has independent pairs and the coordinate short-interval property, but has nonreversible irrational-rotation ergodic components. Thus neither passing symmetry to ergodic components nor inferring ergodicity from coordinate short-interval uniformity is valid.
4. **Subpower-height non-affine projective transformations cannot even send a large integer to an integer.** A reduced-denominator lower bound proves this for every integer matrix, not only positive Stern–Brocot words or a fixed list of label permutations.
5. A factorial-type congruence block preserves all small-prime valuations but **replaces every neighboring largest prime factor by a new prime exceeding the controlled range**. The exact factorization is given below. Congruence reflection is not largest-prime-factor reflection.

These statements have different scopes; none is presented as a counterexample to the entire all-integer stability/Dickman/short-interval package. No `.lean` file, especially `Submission/Spec.lean`, is modified or used as a theorem.

## 1. Natural-prefix laws and the hypotheses that really transfer

Let

\[
 f(n)=\frac{\log P(n)}{\log n}\quad(n\ge2),\qquad
 F(t)=\rho(1/t),\quad F(0)=0,
\]

and choose any bounded extension at the remaining integer indices. Let `T` be the shift on `[0,1]^Z`, with `(Tz)_h=z_{h+1}`, and let

\[
 \mu_X=\frac1X\sum_{n=1}^{X}\delta_{(f(n+h))_{h\in\mathbb Z}}.
 \tag{1}
\]

All weak subsequential limits are stationary: translating a fixed cylinder average changes only a bounded number of endpoints. Their coordinate marginal is `F` by the one-variable Dickman theorem.

The given all-scale diagonal nonconcentration implies

\[
 \mu\{z_0=z_1\}=0                                         \tag{2}
\]

for every **natural-prefix** limit. To check the direction of weak-convergence inequalities, apply Portmanteau to the open strip `|z_0-z_1|<eta`, bound it by the empirical closed strip of width `eta`, and then let `eta` decrease to zero. Bounded ordering tests therefore pass to these limits.

For `n>=3`, the signs of `f(n+1)-f(n)` and `P(n+1)-P(n)` agree. If `p=P(n+1)>q=P(n)`, then

\[
 \log(p/q)\ge\log(1+1/q)\ge\log(1+1/n)
 \ge f(n)\log(1+1/n).
\]

Equality throughout can occur only for the consecutive primes `n=2, n+1=3`; the decreasing case is immediate. Thus pair reversal of every limit in (1) would indeed imply the target, but is stronger than just vanishing of the ordering current.

### Coordinate short intervals are not ergodicity

The available all-scale short-interval theorem says, for fixed continuous `phi` and `u(n)=phi(f(n))-integral phi dF`,

\[
 \lim_{L\to\infty}\limsup_{X\to\infty}
 \frac1X\sum_{n\le X}
 \left|\frac1L\sum_{r=1}^L u(n+r)\right|^2=0.             \tag{3}
\]

The fixed-progression version is available too. A checked source is Tao–Teräväinen, arXiv:1904.05096, definition at `main.tex:214–220` and application at `1127–1134`. Boundedness upgrades the stated averaged L1 estimate to L2.

For each fixed L the integrand is a continuous cylinder function, so (3) transfers to **every** limit in (1). The mean ergodic theorem gives precisely

\[
 \mathbb E_\mu[\phi(z_0)\mid\mathcal I_T]=\int\phi\,dF,
 \tag{4}
\]

and the progression version gives the same conclusion for `I_(T^q)`, for each fixed q. This is a statement about coordinate functions, **not** about arbitrary products of their shifts. It does not say that `mu` is ergodic or totally ergodic. Section 4 gives a model illustrating the distinction.

## 2. An exact smooth-block construction: unique ergodicity is false

The smooth-block phenomenon is known from Balog–Wooley. Here is a self-contained version of the elementary construction, so that its particular quantifiers and dynamical consequence do not depend on an unstated uniformity theorem.

### 2.1 CRT on exponents, not on the integers being counted

**Proposition.** For every integer `H>=1` and every `eta>0`, there are arbitrarily large positive integers N such that

\[
 \max_{|j|\le H}\frac{\log P(N+j)}{\log(N+j)}<\eta.
 \tag{5}
\]

**Proof.** Choose pairwise coprime, odd, squarefree integers `m_1,...,m_H` with

\[
 \frac{\varphi(m_j)}{m_j}<\eta/2.                         \tag{6}
\]

Such choices exist: after excluding any finite set of primes, the product of `(1-1/p)` over a sufficiently long finite set of remaining odd primes is arbitrarily small. Choose the H sets successively and disjointly. This uses only the classical divergence of the sum of prime reciprocals.

Put `M=product_j m_j`, and let S be the primes at most `max(H,2)`. For each `p in S`, solve by CRT

\[
 e_p\equiv v_p(j)\pmod {m_j}\quad(1\le j\le H),
 \qquad 0\le e_p<M.                                     \tag{7}
\]

For all sufficiently large integers t define

\[
 N_t=\prod_{p\in S}p^{e_p+Mt},\qquad
 A_{j,t}=\prod_{p\in S}
 p^{(e_p+Mt-v_p(j))/m_j}.
\]

The exponents defining A are nonnegative integers, and exactly

\[
 \boxed{N_t=j A_{j,t}^{m_j},\qquad
 N_t\pm j=j(A_{j,t}^{m_j}\pm1).}                         \tag{8}
\]

For odd m the cyclotomic factorizations are

\[
 A^m-1=\prod_{d\mid m}\Phi_d(A),\qquad
 A^m+1=\prod_{d\mid m}\Phi_{2d}(A).                       \tag{9}
\]

For `A>=2`, all these factors are positive integers. Since their roots have modulus 1,

\[
 |\Phi_r(A)|\le(A+1)^{\varphi(r)}.
\]

For `d|m` with m odd, `phi(2d)=phi(d)<=phi(m)`. Consequently

\[
 \boxed{P(N_t\pm j)\le
 \max\{j,(A_{j,t}+1)^{\varphi(m_j)}\}.}                  \tag{10}
\]

As `t->infinity`, `A_(j,t)->infinity` and

\[
 \limsup_{t\to\infty}f(N_t\pm j)
 \le \frac{\varphi(m_j)}{m_j}<\eta/2.
\]

Also `P(N_t)<=max(H,2)`, so `f(N_t)->0`. There are only finitely many j, proving (5). QED.

For an exact small illustration, take `H=3`, `(m_1,m_2,m_3)=(3,5,7)`. The solutions for the base primes 2 and 3 are `e_2=21`, `e_3=15`, modulo `M=105`. At t=0,

\[
 N=2^{21}3^{15},\qquad
 N=31104^3=2\cdot432^5=3\cdot72^7.                        \tag{11}
\]

Thus each `N±j`, `1<=j<=3`, has the factorization (9), with maximal factor degrees respectively 2, 4, and 6. The verification script certifies `f(N+j)<9/10` for every `|j|<=3` using integer-power inequalities, without floating-point logarithms or factoring N±j.

### 2.2 Consequences for the actual orbit closure

Apply (5) with `H=l` and `eta=1/l`, choosing `N_l` increasing. Then

\[
 T^{N_l}f\longrightarrow 0^{\mathbb Z}
 \quad\hbox{in the product topology}.                   \tag{12}
\]

Thus the orbit closure K of the actual sequence contains the fixed point `0^Z`, and hence contains the invariant measure `delta_(0^Z)`. It also contains any natural-prefix limit from (1), whose marginal F differs from `delta_0`. Therefore

\[
 \boxed{(K,T)\text{ is not uniquely ergodic.}}             \tag{13}
\]

The same argument rules out an **exact** representation `f(n)=phi(S^n x)` with phi continuous on a uniquely ergodic compact system: its output shift factor would be uniquely ergodic, contradicting (13).

There is also an explicit warning about averaging intervals. Uniform laws on the shifted intervals `[N_l-l,N_l+l]` converge, in the cylinder sense, to `delta_(0^Z)`. For each fixed cylinder radius, discard its bounded number of boundary positions. Thus arbitrary translated Følner intervals do not satisfy the natural-prefix Dickman marginal or diagonal nonconcentration. One cannot silently upgrade the given all-scale prefix statements to uniform-in-position statements.

**Scope.** The point mass in (12) is **not** a natural-prefix limit. This does not disprove uniqueness of the set of natural-prefix limits, nor rule out uniquely ergodic models after modifying the sequence on a zero-density set. Nor does it show that `0^Z` lies in the support of every natural-prefix limit. These stronger assertions are not needed for (13) and are not claimed.

## 3. A natural-prefix limit that cannot have finite tower rank

### 3.1 The precise good-scale input

For every fixed nonzero integer h and rational `a,b in (0,1)`, the known almost-all-scale binary smooth-number result gives

\[
 \frac1X\sum_{n\le X}1_{f(n)\le a}1_{f(n+h)\le b}
 \longrightarrow F(a)F(b)
 \quad\text{outside an exceptional set of log density zero}.
 \tag{14}
\]

For h=1 this is exactly the intermediate result in Tao–Teräväinen, arXiv:1809.02518, Remark `rem1`, `1809.02518.tex:1077–1083`, equation `eq9`. The same deduction for any **fixed** nonzero h is legitimate for the following reasons:

* the structural theorem and the entropy proposition used there already allow arbitrary fixed shifts (choose shifts 0 and h);
* freezing the two smooth cutoffs has the same one-point boundary error, independent of a fixed translation h;
* the required logarithmic binary input explicitly allows any fixed `h!=0`: Teräväinen, arXiv:1710.01195, theorem `theo_bincorr`, line 54, and its smooth-cutoff application;
* replacing the second moving cutoff `n^b` by `(n+h)^b` costs `o(X)` by continuity of the one-variable marginal. This can be checked by discarding bounded n and enclosing the discrepancy in an arbitrarily small fixed exponent interval around b.

This invokes only the established **good-scale** conclusion. It asserts no isotopy or correlation limit at every natural scale, and uses no uniformity in growing h. The stronger existing good-scale theorem, not mere global logarithmic independence, is necessary for the conclusion below about a natural-prefix law. With only global logarithmic independence, the Gram argument would directly concern logarithmic laws instead.

Enumerate all triples `(h,a,b)`. Choose `X_j` arbitrarily large satisfying the first j tests in (14) within `1/j`. This is possible because a finite union of log-density-zero exceptional sets cannot contain every sufficiently large scale. If scales are defined as real numbers, round to integer endpoints at an `O(1/X_j)` cost; this avoids any convention about logarithmic density on the integers versus the reals. Extract a weakly convergent subsequence of the window laws. Continuity of F makes rational-cutoff rectangle boundaries null. The resulting natural-prefix limit `mu_*` satisfies

\[
 \boxed{\mathcal L_{\mu_*}(z_r,z_s)=F\otimes F
        \quad\text{for every }r\ne s.}                  \tag{15}
\]

No higher-order independence is asserted.

### 3.2 Infinitely many orthogonal bilateral shifts

Choose infinitely many real, bounded, continuous, mean-zero orthonormal functions in `L2(F)`. An explicit choice is

\[
 \phi_j(x)=\sqrt2\cos(2\pi jF(x)),\quad j\ge1,
\]

because `F(Z)` is uniform on `[0,1]` when Z has law F. With U the Koopman unitary and `v_j=phi_j(z_0)`, (15) gives exactly

\[
 \boxed{\langle U^r v_i,U^s v_j\rangle
           =1_{r=s}\,1_{i=j}.}                          \tag{16}
\]

Hence the closed spans of the translates of the v_j are mutually orthogonal reducing subspaces, each unitarily equivalent to the bilateral shift on `ell2(Z)`. In particular, the system has infinite Lebesgue spectral multiplicity in this explicit sense.

Here is a direct finite-tower-rank obstruction, without relying on an unstated classification theorem. Suppose the system had tower rank at most R: partitions by levels of at most R Rokhlin towers, with negligible remainder, approximate every measurable function in L2. Apply this to `v_1,...,v_(R+1)`. Project the tower-level approximations onto the reducing space

\[
 W=\overline{\operatorname{span}}
       \{U^n v_j:n\in\mathbb Z,1\le j\le R+1\}.
\]

By (16), Fourier transform identifies W with `L2(T;C^(R+1))`, with U acting by multiplication by the circle coordinate and each v_j the constant standard basis vector e_j. If b_1,...,b_R are the projections of the R tower-base indicators, the projected tower functions lie pointwise in the span of `b_1(z),...,b_R(z)`. That span has dimension at most R. At each z,

\[
 \sum_{j=1}^{R+1}\operatorname{dist}
   (e_j,\operatorname{span}\{b_1(z),...,b_R(z)\})^2\ge1.
 \tag{17}
\]

Integrating contradicts simultaneous L2 approximation of the R+1 vectors. Therefore

\[
 \boxed{\mu_*\text{ has no finite tower rank; in particular it is not rank one.}}
 \tag{18}
\]

This rules out the proposal that **all** natural-prefix systems of f have finite tower rank. It does not rule out finite-rank **ergodic components** of a nonergodic system; Section 4 explains why that distinction is material. It also does not imply positive entropy or full independence.

## 4. A full affine probability model: symmetry need not pass to components

Let U,V be independent Haar variables on `T=R/Z`, set `Q=F^{-1}`, and consider

\[
 Z_n=Q(\{U+nV\}),\qquad n\in\mathbb Z.                    \tag{19}
\]

This is a consistent stationary process, realized by the Haar-preserving transformation `(u,v)->(u+v,v)`.

For distinct r,s, the torus homomorphism

\[
 (u,v)\mapsto(u+rv,u+sv)
\]

has nonzero integer determinant `s-r`, is onto, and therefore sends Haar measure to Haar measure. Consequently every distinct pair in (19) has law `F tensor F`. For centered phi,

\[
 \mathbb E\left|\frac1L\sum_{n=1}^L\phi(Z_n)\right|^2
       =\frac1L\int|\phi|^2\,dF.                       \tag{20}
\]

The same identity holds along every fixed nonzero-step progression. All finite Gram matrices are positive, since these are genuine random variables.

Complete positive integer dilation is also present, at every finite order:

\[
 (Z_{kn})_{n\in\mathbb Z}\overset d=(Z_n)_{n\in\mathbb Z},
 \tag{21}
\]

because `(U,kV)` is again independent Haar. Integer translations and all such dilations therefore preserve the **whole law**.

But V is invariant under time translation, and it is recoverable from the output process by `V={F(Z_1)-F(Z_0)}`. Thus the output law really is nonergodic; V is not just an unobservable auxiliary variable. Conditional on an irrational `V=v`, the time system is an irrational circle rotation and is uniquely ergodic and totally ergodic. Its one-coordinate law is still F, and its conditional current is exactly

\[
 \boxed{\Pr(Z_1>Z_0\mid V=v)=1-v,\qquad
 \mathbb E[\operatorname{sgn}(Z_1-Z_0)\mid V=v]=1-2v.}     \tag{22}
\]

The proof is simply that the rank variable u increases under `u->u+v mod 1` on `[0,1-v)` and decreases on `[1-v,1)`. Q is strictly increasing. For each fixed `v in (0,1)` these two rank displacements stay a positive distance from zero, and continuity of F gives diagonal nonconcentration for that component as well.

Write `nu_v` for the component law. Exactly

\[
 (D_k)_*\nu_v=\nu_{\{kv\}},\qquad
 R_*\nu_v=\nu_{1-v},\qquad
 \mu=\int_0^1\nu_v\,dv.                                 \tag{23}
\]

Thus the complete dilation semigroup acts on the **component parameter**; it need not fix each component. Coordinate short-interval uniformity holds in (20) despite nonergodicity. Positivity and even all-lag pair independence of an averaged law do not force its component currents to vanish.

**Scope.** This is not an arithmetic countersequence, nor a family satisfying the uniform-over-all-natural-limits short-interval bounds for the actual f. It is an exact obstruction to the indicated deductions concerning invariant measures and their components. In particular, it does not contradict the valid whole-law strong-stationarity argument in the next section.

## 5. What a genuinely measure-preserving dilation hypothesis would imply

Suppose a stationary law mu with marginal F satisfies

\[
 \mathcal L(z_0,z_k)=\mathcal L(z_0,z_1)\quad(k\ge1).       \tag{24}
\]

The mean ergodic theorem gives, for bounded phi,psi,

\[
 \mathbb E[\phi(z_0)\psi(z_1)]
 =\mathbb E[\mathbb E(\phi(z_0)\mid\mathcal I_T)
             \mathbb E(\psi(z_0)\mid\mathcal I_T)].       \tag{25}
\]

Without any short-interval hypothesis, the right side is symmetric and is a mixture of product laws. With the actually available coordinate condition (4), it is

\[
 \left(\int\phi\,dF\right)\left(\int\psi\,dF\right).
 \tag{26}
\]

Thus (24) for **every** natural-prefix limit would establish the full ordinary binary Dickman independence conjecture, not merely the requested antisymmetric cancellation. Calling the action “complete multiplicative dilation” does not weaken this consequence.

The actual arithmetic identity, for fixed k, is instead

\[
 \frac1X\sum_{n\le X}\Phi(f(n),f(n+1))
 =\frac1X\sum_{n\le X}\Phi(f(kn),f(kn+k))+o(1).            \tag{27}
\]

It is a conditional law at scale kX, conditioned on the base index being divisible by k. For continuous Phi this follows from the stated stability bound by discarding `n<sqrt X` and then using uniform continuity. Removing the residue condition and returning to the original natural-prefix law are additional requirements. Sections 2–4 provide concrete reasons why broad topological uniqueness, finite-rank classification, or passage to ergodic components cannot supply those requirements automatically.

## 6. A general projective-height obstruction

**Proposition.** Let `a,b,c,d` be integers, `Delta=ad-bc != 0`, and

\[
 \max(|a|,|b|,|c|,|d|)\le K.
\]

If `n>2K^2+K` and `(an+b)/(cn+d)` is a positive integer, then `c=0` and `a/d>0`. Thus the map is affine and orientation preserving at large positive integers.

**Proof.** If `c!=0`, then `|cn+d|>=n-K>2K^2>=|Delta|`. But integrality would imply

\[
 cn+d\mid a(cn+d)-c(an+b)=\Delta,
\]

a contradiction. For `c=0`, nondegeneracy gives `a,d!=0`. Since `n>K`, the sign of `an+b` is the sign of a, so a positive quotient requires `a/d>0`. QED.

More generally, when `c!=0` the reduced denominator q satisfies

\[
 \boxed{q=\frac{|cn+d|}{\gcd(an+b,cn+d)}
          \ge\frac{n-K}{2K^2},}                         \tag{28}
\]

because the gcd divides Delta. If `K=n^{o(1)}`, then `q=n^{1+o(1)}` (use also `q<=K(n+1)`). Clearing this denominator is not a subpower operation. A stability estimate with multiplier q has allowance

\[
 \frac{\log q}{\log(qn)}=\frac12+o(1),                  \tag{29}
\]

not an `o(1)` allowance. This is a failure of the bound to guarantee small error, **not** a lower bound for the actual exponent error.

This treats arbitrary subpower-height integer projective matrices, including ones depending on n. It does not exclude high-height maps, nonlocal averaging, or methods introducing new prime labels. It is distinct from the earlier special triple-label and positive-mediant no-return statements.

## 7. What a factorial congruence block actually preserves

Let `H>=3`, `B=lcm(1,...,H)`, and `L=B^2`. For every prime `p<=H` and every integer `1<=r<=H`,

\[
 v_p(L)>v_p(r),\qquad
 \boxed{v_p(L\pm r)=v_p(r).}                            \tag{30}
\]

Indeed `v_p(B)=floor(log_p H)>=v_p(r)` and is at least 1. It follows exactly that

\[
 L\pm r=r C_r^{\pm},\qquad
 C_r^{\pm}=L/r\pm1>1,\qquad
 \gcd(C_r^{\pm},B)=1.                                   \tag{31}
\]

Every prime divisor of `C_r^±` exceeds H. Therefore

\[
 \boxed{P(L\pm r)>H\ge P(r),\qquad 1\le r\le H.}         \tag{32}
\]

All small-prime valuations match, but **none** of the original largest-prime labels survives as the largest label. In particular, for the frozen cutoff `a_H(n)=1_(P(n)<=H)`, one has

\[
 a_H(r)=1,\qquad a_H(L\pm r)=0\quad(1\le r\le H).
 \tag{33}
\]

This is an explicit obstruction to treating small-prime congruence reflection or a prime-free factorial block as an almost-periodicity theorem for largest-prime cutoffs. The two new rough cofactors in (31) have no supplied ordering relation.

Finally, `log L=2 psi(H)~2H`, so at the destination scale L the controlled cutoff exponent is

\[
 \frac{\log H}{\log L}\sim\frac{\log H}{2H}\longrightarrow0.
 \tag{34}
\]

Thus factorial control of all small-prime divisibility does not access a fixed positive Dickman exponent at the destination scale. Equations (30)–(33) are elementary and do not require the prime number theorem; only the asymptotic description (34) uses `psi(H)~H`.

## 8. Conclusions and verification scope

The requested statement that **every natural-prefix subsequential pair law is reversible remains unproved here**. The complete package of exact multiplicative stability, the Dickman marginal, ordinary averaged short-interval distribution, and diagonal nonconcentration is not disproved by any model in this note.

What has been rigorously ruled out is more specific:

* unique ergodicity of the exact topological orbit closure of f;
* finite tower rank of all of its natural-prefix Furstenberg systems;
* automatic inheritance of reversal/dilation invariance by ergodic components;
* extracting ergodicity from coordinate short-interval means alone;
* positive integer reindexing by non-affine subpower-height projective maps;
* preservation of largest-prime labels by factorial small-prime congruence reflection.

A successful route must retain the original natural-prefix measure and prove a genuine antisymmetric fact about its two-point conditioning, or use additional arithmetic structure not reduced to these mechanisms. No usual logarithmic isotopy theorem has been promoted to an all-natural-scale assertion.

`FurstenbergObstructionVerification.py` checks the exponent-CRT identities, both cyclotomic product identities and integer-power factor bounds, the factorial valuation/rough-cofactor identities, the projective integrality and denominator bounds, and finite-group versions of the affine probability model and its Gram identities. These are finite algebraic checks, not numerical evidence for a new asymptotic cancellation theorem. The infinite constructions and the spectral obstruction are proved above.

The original `Submission/Spec.lean` SHA-256 is `d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.

### Verification record

The final run of `python3 Submission/FurstenbergObstructionVerification.py` passed:

* 2,352 exact exponent-CRT and cyclotomic checks;
* 10,658 factorial valuation/rough-cofactor checks;
* 26,016 projective cases, including 796 positive integral images, all affine and orientation preserving;
* 424 finite-field pair-law checks, plus exact current, Gram, and short-interval mean-square checks;
* 84 rational noncoordinate projection/rank-defect checks.

The explicit block center in (11) is `N=30091839012864`. For offsets `-3,-2,-1,1,2,3`, the largest integer factors in the certified factorizations are respectively `141276239497, 34909326001, 967489921, 967427713, 34748082001, 137405657593`. Each satisfies `factor^10 < (N+offset)^9`; these are upper bounds for the largest prime factors, not asserted prime factorizations.

Python compilation and the equation-tag/display-delimiter audit passed. `Spec.lean` retained the SHA-256 displayed above. No formalization file was changed.
