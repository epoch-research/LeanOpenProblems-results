# Erdős 371: the odd parity coefficient, an arithmetic local-data obstruction, and a small beyond-half range

## Status

This note does **not** prove the requested cancellation for arbitrary
`1/2 < a < b < c < d < 1`, or Erdős 371. It establishes:

1. An exact parity decomposition of the **whole exponent-block sum at X**. The parity factor is reflection-even, but its actual coefficient is reflection-odd. In particular the unknown term is a *twisted* parity correlation, not an unweighted mean of `mu(n(n+1))`.
2. A finite, exact, positive-weight countermodel on actual consecutive integers. It preserves the specified local sieve data, individual prime/parity marginals, and the global product-parity mean, while its signed prime-pair count varies. Its coefficient is an explicit odd character. This refutes automatic cancellation from those data; it is not an asymptotic counterexample to the conjecture or to every possible sieve argument.
3. A precise support obstruction to applying well-factorable prime-progression theorems directly to the prime-modulus coefficient in the switched sum.
4. As a separate genuine all-scale deduction, an application of the Fouvry–Radziwiłł unbalanced-convolution estimate gives cancellation over **full power intervals** if `b < 17/33`. For every fixed `eta>0` the bound is `O(X/(log X)^(1-eta))`. This is a consequence of existing dispersion, not a claimed parity-barrier breakthrough. It also avoids the maximal-cutoff loss in the earlier rough-moment note.

No specification or Lean file is edited or used as an admitted theorem. No unproved Chowla estimate, ordinary prime-pair asymptotic, or prime-graph model is used.

## 1. Exact target, endpoints, and reflection

Fix an integer X and use the prime sets

\[
 I=\{p\text{ prime}:X^a<p\le X^b\},\qquad
 J=\{q\text{ prime}:X^c<q\le X^d\}.
\]

Endpoint conventions for the prime intervals are immaterial, but are fixed here. Write

\[
 F_I(t)=\sum_{p\in I,p\mid t}1,\quad F_J(t)=\sum_{q\in J,q\mid t}1,
\qquad
 D(X)=\sum_{n=1}^{X}\{F_I(n)F_J(n+1)-F_J(n)F_I(n+1)\}.       \tag{1}
\]

For sufficiently large X, these F's take values 0 or 1 on `[1,X+1]`, because the primes exceed `sqrt(X+1)`. Thus (1) is exactly the user's ordered prime-factor-block difference. Nothing below replaces a power interval by one dyadic block.

For an incidence put

\[
 kq-mp=\epsilon,\qquad \epsilon\in\{+1,-1\}.
\]

For `epsilon=+1`, the smaller consecutive integer is `n=mp`; for `epsilon=-1`, it is `n=kq`. In either case `(m,k)=1`, and all cofactors and cutoffs are genuine ones. Requiring both `mp,kq<=X` instead of `min(mp,kq)<=X` changes (1) by its single last edge, of absolute value at most 1.

For fixed p,q, let r be the representative in `[0,pq)` of `p|r, q|r+1`. The opposite representative is

\[
 r'=pq-1-r.                                                    \tag{2}
\]

For the present exponents, eventually `pq>2X+1`; hence at most one representative lies in `[1,X]`. The geometric reflection is `n -> -n-1`, or on the determinant lattice

\[
 (p,q,\epsilon)\longmapsto(-p,-q,-\epsilon),                   \tag{3}
\]

with m,k unchanged. It sends the positive window to a **negative** window. It is not a permutation of the two positive populations at X.

For each fixed coprime m,k, parametrize the two affine forms by a single integer. For every prime ell, their product has

\[
 \rho_{m,k}(\ell)=
 \begin{cases}2,&\ell\nmid mk,\\1,&\ell\mid mk\end{cases}       \tag{4}
\]

roots modulo ell, for either sign. (When ell=2 and m,k are odd, the first case is the usual local obstruction.) More generally the sign change negates both forms and gives a bijection of every complete congruence period. Thus the two singular series agree exactly. This equality says nothing about their incomplete positive-window errors.

## 2. Exact parity projection on the full block sum

Use Liouville's function `lambda(t)=(-1)^Omega(t)` in this section, so that the identities hold without a squarefreeness restriction. Möbius equals Liouville on the squarefree sector; the countermodel below lies entirely in that sector.

Let `mathcal I=(X^a,X^b]` and `mathcal J=(X^c,X^d]` now be intervals of **integer candidate divisors**, not just primes. Set

\[
 z_I=X^{b/3},\qquad z_J=X^{d/3}.
\]

For either interval K, with its indicated z, define

\[
 R_K(t)=\sum_{u\mid t,\ u\in\mathcal K,\ P^-(u)>z_K}1,
\quad
 L_K(t)=\sum_{u\mid t,\ u\in\mathcal K,\ P^-(u)>z_K}\lambda(u),
\]

\[
 C_K(t)=\sum_{u\mid t,\ u\in\mathcal K,\ P^-(u)>z_K}\lambda(t/u).
                                                               \tag{5}
\]

Every candidate u in (5) has `Omega(u)=1 or 2`: three factors exceeding the cube root of its interval's upper endpoint are impossible. Consequently

\[
 F_K(t)=\tfrac12\{R_K(t)-L_K(t)\},\qquad
 L_K(t)=\lambda(t)C_K(t).                                     \tag{6}
\]

These formulas are exact, including prime squares. For functions A,B let

\[
 [A,B]_X=\sum_{n=1}^X\{A(n)B(n+1)-B(n)A(n+1)\}.
\]

Expansion of (1) gives

\[
 4D(X)=[R_I,R_J]_X-[L_I,R_J]_X-[R_I,L_J]_X+[L_I,L_J]_X.        \tag{7}
\]

The last term is **exactly**

\[
 \boxed{
 [L_I,L_J]_X
 =\sum_{n=1}^X\lambda(n(n+1))H_X(n),\qquad
 H_X(n)=C_I(n)C_J(n+1)-C_J(n)C_I(n+1).
 }                                                            \tag{8}
\]

Expanding H recovers precisely the signed cofactor coefficient `epsilon lambda(mk)` on `kq-mp=epsilon`, with p,q replaced by the rough candidate divisors in (5). This is not an arbitrary coefficient introduced after the fact.

Extend the divisor functions in (5) to negative nonzero integers using absolute values, with the same frozen cutoffs X. Then, on the reflected pair of windows,

\[
 H_X(-n-1)=-H_X(n),\qquad
 \lambda((-n-1)(-n))=\lambda(n(n+1)).                         \tag{9}
\]

The same evenness holds for mu. Thus **evenness of the parity factor does not remove (8): its coefficient is odd**. Summing on the union of the positive and negative windows gives zero, but that merely restates the reflection identity; it does not estimate the positive-window sum.

There is no hidden large coefficient here. For `t<=X+1`, the total multiplicity of prime factors exceeding `z_I` is at most `log(X+1)/log z_I=O_b(1)`. Hence `R_I(t), |C_I(t)|=O_b(1)` and similarly for J, so `H_X(n)=O_{b,d}(1)`.

In the elementary four-cell basis `x=lambda(p), y=lambda(q)`,

\[
 1_{p\ {
m prime}}1_{q\ {
m prime}}=(1-x-y+xy)/4.
\]

Antisymmetrizing yields `(epsilon-epsilon x-epsilon y+epsilon xy)/4`, not a projection deleting xy. Reflection and parity are two different involutions. The reflection-odd space still contains `epsilon xy`.

## 3. An exact arithmetic parity trade

### 3.1 Actual integers, factors, and cutoffs

Take

\[
 X=10^6,\quad (a,b,c,d)=(11/20,3/5,3/4,17/20),\quad m=30,\ k=1,
 \qquad q=30p+\epsilon.
\]

Use the following eight actual pairs. A bare number in the factorization column is prime.

| epsilon | p, with factorization | q, with factorization | tau=mu(pq) |
|---:|---:|---:|---:|
| +1 | 1999 | 59971 | +1 |
| +1 | 2137 | 64111 = 61 * 1051 | -1 |
| +1 | 2491 = 47 * 53 | 74731 | -1 |
| +1 | 3763 = 53 * 71 | 112891 = 79 * 1429 | +1 |
| -1 | 2003 | 60089 | +1 |
| -1 | 1997 | 59909 = 139 * 431 | -1 |
| -1 | 3233 = 53 * 61 | 96989 | -1 |
| -1 | 3551 = 53 * 67 | 106529 = 307 * 347 | +1 |

All p's are in `mathcal I`, all q's in `mathcal J`; both exceed `sqrt X`; and all corresponding consecutive integers are at most X. For the plus rows n=30p; for the minus rows n=q. Every `n(n+1)` in the table is squarefree, and

\[
 \mu(n(n+1))=\mu(30)\mu(pq)=-\tau.                           \tag{10}
\]

For each orientation the four rows have primality types `(P,P),(P,S),(S,P),(S,S)`, where S is a product of two distinct primes. All p's satisfy `p=epsilon (mod 6)`, and all q's satisfy `q=31 epsilon (mod 180)`. All p,q are 43-rough. In fact the displayed p factors exceed `X^(b/3)` and the displayed q factors exceed `X^(d/3)`, so these are also valid candidates in the exact projection of Section 2.

### 3.2 The data that are preserved, exactly

For `-1<=theta<=1` give each row weight

\[
 w_\theta=1+\theta\epsilon\tau\in[0,2].                       \tag{11}
\]

For each orientation **separately**, (11) preserves:

* total mass, equal to 4;
* p-prime mass and q-prime mass, each equal to 2;
* each individual mu(p) and mu(q) sum, both equal to 0;
* the corresponding data conditional on **any** residue condition on p modulo 6, q modulo 180, or n,n+1 modulo 180;
* every divisor test `1_{r|p}1_{s|q}` whose r,s have all prime factors at most 43, including arbitrary prime powers and products;
* likewise every such divisor test on n,n+1, also when multiplied by either individual primality indicator.

Proof: within one orientation all local tests just described are constant on the four rows. The parity vector is `(1,-1,-1,1)`, which has zero sum and is orthogonal to both individual-prime columns `(1,1,0,0)` and `(1,0,1,0)`. For n,n+1 the small-prime valuations are fixed: the multiple of 30 has valuations 1 at 2,3,5 and 0 at every other prime at most 43; the other integer has none of these prime factors. The n residue modulo 180 is 30 for the plus rows and -31 for the minus rows.

For an implementation on the **full actual candidate interval**, start with unit weights on all integer p in `mathcal I` with `30p+epsilon in mathcal J`, and modify just the eight displayed points by (11). All the stated local sums and individual-prime sums remain exactly their original arithmetic values. In particular their original main terms and remainders, whatever those are, are unchanged. This is a local-data countermodel, not a modification of what the genuine primes are.

### 3.3 What changes, and the odd character

The weighted prime-pair counts on the four rows are

\[
 S_+(\theta)=1+\theta,\qquad S_-(\theta)=1-\theta,
 \qquad S_+(\theta)-S_-(\theta)=2\theta.                      \tag{12}
\]

In the full-interval implementation the original difference is changed by `2 theta`. On the eight-point support, at `theta=+1` all pair mass is in the plus orientation; at `theta=-1` all is in the minus orientation. All prime tests here use actual primality, not assigned labels.

Moreover the **global product-parity mean is unchanged**:

\[
 \sum_{\text{eight rows}}w_\theta\mu(n(n+1))=0
 \quad\text{for every theta}.                               \tag{13}
\]

More strongly, this remains unchanged after inserting **any reflection-even function of n modulo 180**: its values at 30 and -31 agree, and the two orientation-specific parity changes cancel. Thus even local product-parity information can be supplied as additional data without detecting the trade.

Let `chi_3` be the real nonprincipal character modulo 3, so `chi_3(-1)=-1`. Because the two positive orientations have n congruent to 0 and -1 modulo 3, respectively,

\[
 \epsilon=\chi_3(2n+1),\qquad
 w_\theta-1=-\theta\chi_3(2n+1)\mu(n(n+1)).                  \tag{14}
\]

Here mu of the product is reflection-even while chi_3 of `2n+1` is reflection-odd. The twisted parity mean is

\[
 \sum_{\text{eight rows}}w_\theta\chi_3(2n+1)\mu(n(n+1))
 =-8\theta.                                                  \tag{15}
\]

On these eight points, the factorization lists also show that the only rough divisor in the I interval on the `30p` side is p, and the only rough divisor in the J interval on the q side is q; the cross-interval rough-divisor counts vanish. Consequently the **actual coefficient in (8)** is `H_X(n)=-epsilon` on every displayed point. Under (11) the first three terms of (7) are unchanged, while the last changes by `8 theta`. Thus this trade applies to the specific arithmetic parity projection, not just to an abstract four-cell analogy. All composite p and q in the table have largest prime factor below `X^a`, so the individual actual LPF-bin marginals at n and n+1 are preserved too.

One can therefore also put these weights directly on all integers `1<=n<=X`, leaving every other integer at weight 1. In the **rough candidate universe (5)**, the selected indices affect only the cofactor family `(m,k)=(30,1)`. Thus the specified local data can be conditioned on each cofactor pair without exposing this trade: all other families are unchanged. This assertion concerns the rough universe (5), not every unsifted integer-divisor representation of the selected n.


Thus the only four-cell component not fixed by mass and the two individual prime/parity marginals can have a **purely antisymmetric** defect, despite (13). This directly addresses the proposed claim that a product-parity defect must be symmetric.

The countermodel can even preserve **global reflection invariance of the ambient weights**, if that is added to the data. Let S be the eight positive indices, put `S_tilde=S union {-n-1:n in S}`, and on this symmetric support define

\[
 h_{\rm even}(n)=-\operatorname{sgn}(2n+1)\chi_3(2n+1)
                       \mu(n(n+1))1_{\widetilde S}(n).        \tag{15a}
\]

Both the sign and the character change under reflection, so `h_even(-n-1)=h_even(n)`. On S it is exactly `epsilon tau`. Thus the globally reflection-even, nonnegative weights `1+theta h_even` give precisely the same positive-window countermodel. This also shows why evenness of an *entire ambient parity defect*, not just of mu, would still not imply the desired positive-window symmetry. It pairs a positive orientation with the opposite **negative** orientation. No negative point is counted in (12). When the perturbation is added to an ambient arithmetic sequence, its global mu sum retains its original value exactly; no value or asymptotic for that original sum is assumed.

### 3.4 Finite linear-programming obstruction and its scope

Let V be generated by the orientation-specific tests of Section 3.2 together with the global reflection-even product-parity tests just described. The vector `v=epsilon tau` is in the exact nullspace of this data map, but its pairing with the signed prime-pair target is 2. The two nonnegative measures `1+v` and `1-v` therefore have identical V-data and target values +2 and -2 on this support. This is an explicit dual obstruction to deducing the target from these local data by any linear combination, irrespective of its coefficients.

In particular, if U,L belong to the preserved local/one-prime span and pointwise majorize/minorize the pair-prime indicator on a four-row orientation, their common-data gap is at least 2: one compatible measure has pair mass 2, another has pair mass 0.

**Limit of the obstruction.** This finite example does not have `cX` disjoint trades for unbounded X, does not preserve every divisor datum through a growing power level, and does not satisfy an asserted asymptotic-sieve Type-II hypothesis. It does not disprove `D(X)=o(X)`. It disproves the automatic algebraic/local claim about the symmetry of every parity defect, even after the listed one-prime and global-parity information is supplied. A proof using stronger growing-level or bilinear information is not excluded.

## 4. Why common upper/lower weights do not cancel their gap

Let `T=1_{p prime}1_{q prime}`, and suppose common sieve expressions `L<=T<=U` are valid on both candidate populations. Write their summed values as `L_sigma,U_sigma`, and the true counts as `S_sigma`. The valid comparison is

\[
 L_+-U_-\le S_+-S_-\le U_+-L_-.                              \tag{16}
\]

If the local main terms of U are `M_U` in both orientations, and those of L are `M_L` in both orientations, (16) retains the **positive gap `M_U-M_L`**. Subtracting the two upper bounds is not a valid inequality.

Equivalently, with the upper slack `E_sigma=U_sigma-S_sigma>=0`,

\[
 D=U_+-U_--(E_+-E_-).                                        \tag{17}
\]

Equality of the U main terms does not control the last difference. The arithmetic trade provides compatible data for which those slacks change in opposite directions. Constructing a signed approximation without separate pointwise bounds could still work, but then its correlation with the odd parity coefficient (8) is new information to prove.

## 5. Switching, characters, and the well-factorability issue

### 5.1 Exact switching and character formula

Let

\[
 E_J(Y;p,r)=\sum_{t\le Y,\ t=r\bmod p}F_J(t).
\]

Changing variables `t=kq` in (1) gives

\[
 D(X)=\sum_{p\in I}\{E_J(X;p,1)-E_J(X;p,-1)\}
       +F_I(X)F_J(X+1).                                    \tag{18}
\]

The last term is 0 or 1. Expanding the large-prime divisor in F_J gives exactly

\[
 \boxed{
 D(X)=2\sum_{p\in I}\frac1{p-1}
 \sum_{\chi\bmod p,\ \chi(-1)=-1}
 \sum_{q\in J}\chi(q)\sum_{k\le X/q}\chi(k)
 +F_I(X)F_J(X+1).
 }                                                          \tag{19}
\]

All characters here have prime conductor p. Formula (19) follows from ordinary character orthogonality: the coefficient of a character is `1-chi(-1)`, not zero for the odd characters. It involves no unproved distribution statement. The cutoff `kq<=X` is retained.

For fixed k, a direct prime-progression interpretation has modulus `p>X^(1/2)` and prime range at most `X/k<=X`, so the ordinary Bombieri–Vinogradov range misses it. Switching again preserves the second prime test; it does not make that test disappear. Oddness removes the principal character but not the long-conductor character sums in (19). The character in the finite countermodel is an illustration of the odd-parity mechanism, not a claim that conductor 3 occurs in (19).

### 5.2 An exact support lemma

If a sequence `omega_r` is well-factorable of level Q in the usual sense, choose the permitted factorization `Q=sqrt(Q)*sqrt(Q)`. Thus

\[
 \omega_r=\sum_{uv=r}\alpha_u\beta_v,
 \qquad \alpha_u=\beta_u=0\quad(u>\sqrt Q).
\]

For a prime `p>sqrt Q`, neither factorization `p=1*p=p*1` is supported. Consequently

\[
 \boxed{\omega_p=0\qquad(p>\sqrt Q).}                        \tag{20}
\]

The same is true for any linear combination of such sequences; triply well-factorable weights have an even stronger balanced support restriction. The definition was checked in Maynard, *Primes in arithmetic progressions to large moduli II: Well-factorable estimates*, arXiv:2006.07088, `WellFactorable.tex:39–50`.

The coefficient `1_{p in I}` in (18)–(19) is therefore not a well-factorable sequence at any level `Q<X^(2a)`. Since `2a>1`, the usual levels below the length X cannot represent it directly. This is a precise reason that inserting a BFI/Maynard theorem for well-factorable weights does not estimate this prime-modulus sum. One can instead sieve the modulus variable, but then one must control the extra nonprime configurations and the signed upper/lower gap, not just quote factorability.

### 5.3 What an asymptotic sieve would need

Asymptotic-sieve parity removal uses additional information about divisor convolutions/bilinear forms. It does not say that every unresolved error is a constant multiple of one global Möbius mean. For example the Friedlander–Iwaniec bilinear hypothesis, as recorded in Ford, *On Bombieri's asymptotic sieve*, arXiv:math/0401215, equation `bilinear` (`math0401215.tex:151–168`), controls sums of `mu(mn) a_mn` with nonconstant divisor coefficients, uniformly in a range of the variables. A bare bound for `sum mu(n)a_n` is not that hypothesis.

Applying a divisor identity to the difference of the two determinant populations is legitimate. But it produces the **signed versions** of those bilinear sums. Reflection relates them to negative windows; it does not prove their positive-window estimates. Already the exact identity (8) supplies a bounded, reflection-odd cofactor coefficient. The finite trade shows that controlling the mass, the individual prime/parity components, and a global product-parity sum still need not control that coefficient. No general impossibility theorem for asymptotic sieves is being asserted here.

## 6. A genuine all-scale partial range: b < 17/33

This section uses an established dispersion estimate, not the countermodel. It proves cancellation for a nonempty family of the actual full-power blocks.

### Proposition

For fixed

\[
 1/2<a<b<\min(c,17/33),\qquad c<d<1,
\]

and every fixed `eta>0`,

\[
 \boxed{D(X)\ll_{a,b,c,d,\eta} X(\log X)^{-1+\eta}.}          \tag{21}
\]

It suffices to take `0<eta<1`. No asymptotic for either orientation individually is used.

### Analytic input and uniformity

Fouvry–Radziwiłł, *Level of distribution of unbalanced convolutions*, arXiv:1811.08672, `FouvryRadzi7.tex:66–77`, Corollary `cor:Main(i)`, gives an arbitrary logarithmic saving for a divisor-bounded convolution on `t<uv<=2t`, averaged over moduli `Q<r<=2Q`, if the short factor is Siegel–Walfisz and its size N satisfies

\[
 \exp((\log t)^\rho)\le N\le Q^{-11/12}t^{17/36-\rho}.         \tag{22}
\]

We use fixed residues +1 and -1, not a maximum over residues.

For a frozen cutoff `z>=2` put `g_z(n)=1_{P(n)<=z}`. Its restriction to primes is Siegel–Walfisz **uniformly in z**: a truncation of a prime interval adds only an endpoint in the prime Siegel–Walfisz estimate. The proof below uses that uniform endpoint estimate, not an unproved theorem uniform over arbitrary multiplicative functions. The additional coprimality parameter in the cited Siegel–Walfisz definition is harmless for a prime sequence: the removed primes divide that parameter and their number is bounded by its permitted divisor-function factor.

### Prime-modulus estimate, retaining the exceptional-set weight

For `p in I`, define

\[
 B_z(X;p,r)=\sum_{n\le X,n=r\bmod p}g_z(n)
 -\frac1{p-1}\sum_{n\le X,(n,p)=1}g_z(n).
\]

We claim, uniformly in the cutoff z, that

\[
 \sum_{p\in I}|B_z(X;p,\pm1)|\ll X(\log X)^{-1+\eta}.        \tag{23}
\]

Here is a proof retaining the pointwise exceptional-set bound; merely summing the published weak dyadic multiplicative-function corollary would lose the saving.

Write `L=log X` and discard `n<=X/L^K`. By elementary progression counting its total contribution to (23) is

\[
 \ll (X/L^K)\sum_{p\in I}1/p+\#I\ll X/L^K+X^b,              \tag{24}
\]

and the subtracted means have the same bound without the `#I` term.

On each remaining interval `t<n<=2t`, put `delta=17/33-b` and choose `0<sigma<min(eta,delta/100)`. For sufficiently large X all the modulus blocks satisfy `Q<=t^(b+delta/2)`. Set

\[
 U=\exp((\log t)^\sigma),\qquad V=t^\sigma.
\]

Partition `(U,V]` into prime intervals of relative length comparable to `(log t)^(-B)`, for a sufficiently large fixed B. Call n good if it has a prime factor in `(U,V]` and its **first occupied** small interval contains exactly one prime factor, counted with multiplicity. A good n has a unique decomposition

\[
 n=u r v,
 \quad P(u)\le U,\quad r\text{ prime in the first occupied interval},
 \quad P^-(v)>\text{that interval's upper endpoint}.           \tag{25}
\]

For each interval (25) is a convolution of the short prime coefficient `1_{r<=z}` with an arbitrary 1-bounded cofactor coefficient, since u is uniquely the U-smooth part of the cofactor. Dyadic localization gives the format of (22), including `t<n<=2t`. The identity

\[
 17/36-(11/12)(17/33)=0
\]

and the choice `rho=sigma/2` leave upper-exponent margin `11 delta/24-sigma/2>sigma`, so (22) holds for all the needed prime intervals and modulus blocks. For the two cutoffs actually used, `z=X^c,X^d`, every extracted short prime is below z; the prime sequence in this application is thus independent of the moving cutoff. The polynomial-in-log number of intervals/blocks is absorbed by the arbitrary logarithmic saving. Thus the good part of (23) is `O_A(X/L^A)` for any fixed A.

The complement of (25) is bounded **pointwise in p**, uniformly in z, by

\[
 \ll \frac{t}{p-1}
       \{(\log t)^{-1+\sigma}+(\log t)^{1-B}\}.              \tag{26}
\]

For no prime factor in `(U,V]`, this is Shiu's upper bound applied to the multiplicative exclusion indicator, whose prime product has relative size `O(log U/log V)`. This is also the argument in the cited paper's Lemma `le:trivialS`, lines 1031–1056. The second exceptional case has two primes r,s in one small interval. Since `rs<=t^(2 sigma)` and `p<=t^(3/4)` with room to spare, the progression count for `n=rs v` is `O(t/(p rs))`; its rounding error is absorbed. Brun–Titchmarsh bounds each small-interval prime reciprocal sum by `O((log t)^(-B))`. Summing its square over `O((log t)^(B+1))` intervals gives the second term of (26). This includes repeated primes. The subtracted mean is bounded in the same way by first taking modulus 1 and then dividing by p-1.

Crucially,

\[
 \sum_{p\in I}\frac1{p-1}=\log(b/a)+o(1)=O_{a,b}(1).          \tag{27}
\]

Sum (26) using (27), and then sum the n-intervals geometrically. Choose `sigma<eta`, B and K sufficiently large. This proves (23).

Finally, because `c>1/2`, for every `n<=X` the large-prime-block indicator is exactly

\[
 F_J(n)=g_{X^d}(n)-g_{X^c}(n).                               \tag{28}
\]

Apply (23) at these two frozen cutoffs. The principal means at residues 1 and -1 agree and cancel. Equation (18), including its bounded endpoint, proves (21).

This argument estimates the entire p power interval at once through its bounded harmonic mass (27). It does not make the invalid inference that `O(X/log^2 X)` for one dyadic p,q rectangle can be summed over all rectangles without loss. No claim is made for `b>=17/33` by this argument.

## 7. Verification and conclusion

`AntisymmetricSieveVerification.py` independently checks:

* exact integer-power membership, primality/factorizations, determinant equations, and squarefreeness for all eight rows;
* the preserved local divisor/residue data and individual marginals, with nonnegative weights 0,1,2;
* the global parity mean and the nonzero odd-character-twisted parity mean;
* whole-block arithmetic counts, the endpoint in (18), the cofactor identities, the parity decomposition (7)–(8), and reflection (9), at several finite X;
* the local root counts and finite odd-character orthogonality;
* the balanced-support obstruction (20).

The recorded run passed 702,144 local divisor/residue/marginal equalities, 6,560,043 full-block divisor/parity/reflection checks, 25,261 actual cofactor/CRT incidence checks, 3,648 exhaustive CRT pair checks, 2,805 local-root sign checks, 7,708 finite odd-character checks, and 474 balanced-factorization support checks. In particular the nonzero endpoint in (18) was tested at `X=1003`, where `X=17*59` and `X+1=4*251`. The globally reflection-even extension and all even local parity tests were checked too.

Finite checks verify the algebra, not the analytic dispersion theorem or a conjectural limiting density. The results are in `AntisymmetricSieveVerification.log`. The character-root tests use complex floating-point roots; the parity trade, factorization, cutoff, divisor, endpoint, and cofactor tests use exact integer arithmetic. No Lean formalization of these analytic deductions is claimed.

The surviving task for general ordered exponent blocks is still `D(X)=o(X)`. The parity-even observation alone does not prove it: the exact arithmetic coefficient is odd, and there is an explicit arithmetic local-data trade in that odd channel. Conversely this does not rule out proving the needed signed Type-II/cofactor correlation by additional analytic information.

`Submission/Spec.lean` was left unchanged, with SHA-256
`d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.
