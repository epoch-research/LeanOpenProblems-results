# Fully centered composite displacement: transport and spectral audit

## Result

**The proposed uniform spectral amplification fails, unconditionally, for the stated operator.** This is not the earlier singly-centered-composite variance obstruction. If `X` omits `o(N/log² N)` vertices and all the composite displacements are `o(N)`, then, using only interior prime rows,

\[
 \boxed{\quad \|B_k|_X\|/E_k\ \geq\ (2-o(1))/\sqrt{\log N}.\quad}                 \tag{A}
\]

For the pool in the question the stronger, trimming-stable bound is
`(2-o(1)) exp(-L/2) = (log N)^(-1/20+o(1))`. It holds for **every** such `X`, including growing `k`. Thus a uniform normalized bound `o(1/log N)` on an adequately large good set is false, not merely an unavailable operator theorem.

The multiplicative transport is nevertheless exact. Its proper-divisor terms are not exclusively long-shift cofactor correlations. An additional, norm-contractive **equal-smooth-part pinching** does isolate the original shift and explicit long shifts. A genuine elementary bound for that changed operator is proved below; its lift-norm cost prevents the claimed amplification. None of these statements proves or disproves Erdős #5 or a prime-pair asymptotic.

## 1. Exact transport, coefficient extraction, and triangular inversion

Write `V=(N,2N] ∩ Z`, with inner product normalized by `1/N`. Let
`M_j(P)` be the unordered squarefree products of `j` distinct pool primes,
`M_0={1}`, `E_j=Σ_{m∈M_j}1/m`, and `L=E_1`. Assume `1≤k≤|P|`, `P⊂[H_0,H]`, `H<y`, and `h≠0`; replace `h` by `|h|` when necessary. All operators below have **genuine displacement** `±hm`, never an additive path displacement. Vertex functions are zero-extended when applying the operator, but the multiplicative lifts below are defined on **all positive integers**, with interval masks imposed separately. Compression means `B_k|_X=1_X B_k 1_X` for the same set `X⊂V` at both ends. Symmetry follows from `c_m(n±hm)=c_m(n)`.

For numerical comparisons the regime is
`t=log log N`, `log H=(log N)^(2/5)`, `log H_0=(log N)^(3/10)`,
`P={primes in [H_0,H]}`, `|h|=O(log N)`, and `k=O(t)`.
Thus `L∼t/10`, `|h|H^k=N^{o(1)}`, and eventually no pool prime divides `h`.
(The case `h=0` is a diagonal multiplication operator, not a prime-gap transport.)

For positive integers let `s_y(n)` be the entire `y`-smooth part, including prime powers, and `r_y(n)=n/s_y(n)`. Take arbitrary functions `a,b` on the `y`-rough positive integers (including 1 if wanted), and put

\[
 F_z(n)=z^{\Omega(s_y(n))}a(r_y(n)),\qquad
 G_w(n)=w^{\Omega(s_y(n))}b(r_y(n)).
\]

Thus `F_z(du)=z^{ω(d)}F_z(u)` for every pool product `d`, even when `d` and `u` share factors. Use a bilinear, not Hermitian, generating function
`H_k(z,w)=N^{-1}Σ_n F_z(n)(B_k|_X G_w)(n)`.
For a pool product `d` and an integer shift `s`, define

\[
 C_{d,s}(z,w)=\frac1N\sum_{\sigma=\pm1}\sum_{u\geq1}
 1_X(du)1_X(d(u+\sigma s))F_z(u)G_w(u+\sigma s),                 \tag{1}
\]

with nonpositive arguments excluded. In particular the cofactor interval is **exactly** `(N/d,2N/d]`, with its shifted endpoint also in that interval; the masks are `X(du)`, not `X(u)`.

The complete expansion is

\[
\boxed{
 H_k(z,w)=\sum_{j=0}^k(-1)^{k-j}(zw)^j
 \sum_{\substack{d\in M_j,\ e\in M_{k-j}\\(d,e)=1}}
 \frac1e\,C_{d,he}(z,w).}                                    \tag{2}
\]

**Proof.** For `m=de`,
`c_m(n)=Σ_{d|m} μ(m/d)/(m/d) · 1_{d|n}`. Substitute `n=du`; the other endpoint is `d(u±he)`. Multiplicativity supplies `(zw)^j`. This proof retains every boundary and mask. If (1) is instead normalized by the cofactor length `N/d`, each summand in (2) has harmonic factor `1/(de)=1/m`, explaining the unordered normalization `E_k`. Arbitrary extra endpoint masks pull back in precisely the same way. A joint edge mask must also be pulled back; it is not automatically covered by an endpoint-compressed norm inequality.

### What the proper-divisor terms actually contain

Set `w=z`, as in the question, and extract `[z^(2k)]`. In the term with `ω(e)=ℓ=k-j`, this extracts `[z^(2ℓ)]` from (1). Explicitly it is a sum over

\[
 A,B\text{ y-smooth},\quad \Omega(A)+\Omega(B)=2\ell,\qquad
 r,s\text{ y-rough},\quad Bs-Ar=\sigma he,                     \tag{3}
\]

weighted by `a(r)b(s)1_X(dAr)1_X(dBs)`. The stronger two-variable extraction `[z^k w^k]` replaces the degree condition by `Ω(A)=Ω(B)=ℓ`; it does **not** force `A=B`. These are unequal-coefficient affine correlations when `A≠B`, not ordinary long-shift correlations of `a,b`. All congruence restrictions are part of the equation in (3).

For `e=1` one obtains the rough-cofactor shift `h`. But **every proper-divisor term also contains that same shift**, through `A=B=e`. For a fixed original `m`, these copies combine with coefficient

\[
 \sum_{e\mid m}\mu(e)/e=\varphi(m)/m,
\]

not zero. Their aggregate is exactly the component with `s_y(n)=s_y(n±hm)=m`:

\[
 \frac1N\sum_{m\in M_k}\frac{\varphi(m)}m
 \sum_{\substack{\sigma=\pm1,\ r,r+\sigma h\ \text{y-rough}}}
 1_X(mr)1_X(m(r+\sigma h))a(r)b(r+\sigma h).                    \tag{4}
\]

Other equal-smooth-part terms have `A=B=q`, `q|he`, and shift `he/q`. Unequal smooth parts remain in general. Evaluating at `z=0` keeps the zero-small-factor, displacement-`hm` term; it does not recover (4). Coefficient extraction from a norm bound costs the usual `r^(-2k)` on `|z|=r`, or the corresponding two-radius factor. A Hermitian norm bound applies to the bilinear form by conjugating one argument, not by conjugating the generating variable in (2).

### The exact triangular system exists, but does not leave just the top order

Let `D_{j,s}^Q` have weight `1_{d|n}` and displacement `±sd`, summed over `d∈M_j(Q)`. Define `B_{j,s}^Q` with weight `c_d`, including `B_{0,s}=D_{0,s}`. All are compressed to the **same** `X`. Boolean-lattice inversion gives

\[
\begin{aligned}
 B_{k,h}^{P}&=\sum_{\ell=0}^k(-1)^\ell
  \sum_{e\in M_\ell(P)}\frac1eD_{k-\ell,he}^{P\setminus\{p:p\mid e\}},\\
 D_{k,h}^{P}&=\sum_{\ell=0}^k
  \sum_{e\in M_\ell(P)}\frac1eB_{k-\ell,he}^{P\setminus\{p:p\mid e\}}.       \tag{5}
\end{aligned}
\]

For each fixed `m`, the inverse is simply
`1_{m|n}=Σ_{d|m} c_d(n)/(m/d)`. There are no missing factorials. Removing the `j=0` translation term from the second identity reconstructs exactly the singly-centered operator with weight `1_{m|n}-1/m`. It requires **all** proper centered orders, including order one, with different pools and shifts `he`. For `k≥2`, uniqueness of the multilinear basis on the divisibility patterns modulo `m` forbids replacing this hierarchy by just `B_k` and the bare translation term. Special masks can change which patterns survive, but must be stated and analyzed, not canceled formally.

## 2. An honest isolation variant: pinch by the exact smooth part

There is a useful positive algebraic statement, distinct from (5). Assume `(h,∏_{p∈P}p)=1`, as holds in the proposed regime. Let `P_s` project onto `s_y(n)=s`, and define

\[
 \mathcal C_k=\sum_{\Omega(s)=k} P_s(B_k|_X)P_s.
\]

This is an orthogonal direct sum of compressions, so `||C_k||≤||B_k|_X||`. Equivalently, average conjugations by independent unit phases for each prime at most `y`, then restrict to `Ω(s)=k`. A single scalar phase would enforce only equal `Ω`, not equal smooth parts. On a nonzero block necessarily

\[
 s=dv,\quad d\in M_{k-\ell}(P),\quad v\mid h,\quad
 \ell=\Omega(v),
\]

and `d` is the full pool-prime part of `s`, squarefree. Indeed, equal smooth parts at both endpoints imply `s|hm`. Writing `n=sr`, the block is **exactly**

\[
 (\mathcal C_k f)_s(r)=(-1)^\ell\frac{\varphi(d)}d
 \sum_{\substack{e\in M_\ell(P\setminus\{p:p\mid d\})\\\sigma=\pm1}}
 \frac1e f_s\bigl(r+\sigma(h/v)e\bigr),                        \tag{6}
\]

with both cofactors `y`-rough and both lifted endpoints in `X∩V`. All other blocks vanish. The case `v=1` is precisely (4); when `v>1`, every remaining cofactor shift is at least `H_0`. Thus **pinching really does give original-shift plus long-shift terms**. It is an additional operator operation, not a cancellation of the unequal-smooth-part terms of (2).

This also gives an actual, proved spectral estimate by the absolute row-sum bound:

\[
 \|\mathcal C_k\|\leq
 2\max_{\substack{v\mid h,\ \ell=\Omega(v)\leq k\\d\in M_{k-\ell}(P)}}
       \frac{\varphi(d)}d E_\ell(P\setminus\{p:p\mid d\}).       \tag{7}
\]

For fixed `h` this is `O_h((1+L)^{Ω(h)})`. When `y>2`, an odd cofactor shift gives no rough-to-rough edge. For example, at `h=2` the `v=2` blocks vanish, and (7) improves to `2`. More generally, retaining **only** blocks `s∈M_k(P)` gives an operator `C_k^P` of norm at most `2` and exactly the shift-`h` blocks, for every `h` coprime to the pool.

This valid improvement does **not** yield the desired relative estimate. For `y=N^θ`, `1/3<θ<1/2`, `H^k=N^{o(1)}`, use the economical lifts

```
F^[k](n) = 1_{s_y(n)∈M_k(P)} 1_Prime(r_y(n)),
G^[k](n) = 1_{s_y(n)∈M_k(P)} 1_{r_y(n)>1} λ(r_y(n)).
```

Single-integer counting gives

\[
 \|F^{[k]}\|_2^2\sim E_k/\log N,\qquad
 \|G^{[k]}\|_2^2\asymp E_k/\log N.                            \tag{8}
\]

For the first, sum `π(2N/m)-π(N/m)` over the uniquely determined smooth part `m`; PNT is uniform for `m≤N^{o(1)}`. For the second, rough cofactors are prime or semiprime; the prime lower bound and the sum over two primes exceeding `y` give the same order. Thus the proved norm bound `2` gives an absolute bilinear budget `O(E_k/log N)`, whereas the transported prime-pair benchmark is `E_k/log² N`. The degree gain has canceled. Coefficients on the lifts cannot improve this ratio: Cauchy–Schwarz compares `Σ u_m v_m φ(m)/m²` with `(Σ|u_m|²/m)^(1/2)(Σ|v_m|²/m)^(1/2)`.

By (8), a norm-only relative error would require the **unnormalized** pinched norm to be `o(1/log N)`. But a retained edge in a desired block has weight `φ(m)/m`, which is `1-o(1)` in the displayed regime, so that block has norm at least `1-o(1)`. Such a small bound would force all those edges to be absent. This is a conditional matrix observation, **not** a claim that a specified prime/rough pair exists. Pinching provides no parity-specific cancellation on these positive-weight blocks.

## 3. Further arithmetic norm lower bounds on the full interval

These bounds concern `B_k`, not its pinched version. Set
`q_p=1/p`, `v_p=q_p(1-q_p)`,
`W_j=Σ_{m∈M_j}∏_{p|m}v_p`, and `S_j(n)=Σ_{m∈M_j}c_m(n)`.
Under uniform CRT averaging the centered monomials are orthogonal:

\[
 \mathbb E(S_iS_j)=1_{i=j}W_j.
\]

In the proposed regime, for `k=O(t)`, all the following finite-interval moment errors, including boundaries, are `N^(-1+o(1))`. To see this without averaging over the enormous full primorial, expand the divisor indicators: there are at most `(C H)^{3k}` terms in the largest moment below, each CRT progression count has error `O(1)`, and the boundary strip has length at most `2|h|H^k`. A common error bound is `O((1+|h|)(C H)^{4k}/N)`. Also, uniformly for `j≤k`,

\[
 W_j=(1+O(j/H_0))E_j,\qquad
 E_j=\frac{L^j}{j!}\left(1+O\left(\frac{j^2}{H_0L}\right)\right).           \tag{9}
\]

The latter follows by bounding repeated labels in the ordered expansion of `L^j`, using `Σ_p1/p²≤L/H_0`.

* **Constant test:** away from boundaries `B_k1=2S_k`, hence
  `||B_k||≥(2-o(1))√E_k`, improving the two-step trace constant `√(2E_k)`.
* **Divisor-polynomial tests:** for `i+j=k`, CRT gives exactly
  `E[S_i(n)(B_kS_j)(n)]=2 binom(k,i)W_k`. Every prime of an edge label must occur in one of the two test monomials; the total degree forces those monomials to partition the label. Consequently

  \[
  \|B_k\|\geq(2-o(1))\binom{k}{i}\frac{W_k}{\sqrt{W_iW_j}}
       =(2-o(1))\sqrt{\binom{k}{i}E_k}.                        \tag{10}
  \]

* **A stronger growing-order count test:** for fixed `x>0`, let
  `T_{x,k}=Σ_{j=0}^k x^j S_j`. If no pool prime divides `h`, then

  \[
  \|B_k\|/E_k\geq(2-o(1))(2x+x^2)^k e^{-x^2L}.                \tag{11}
  \]

  Here is a proof, including the normally discarded correlations. Its squared test norm is `Σ_{j≤k}x^{2j}W_j≤e^{x²L}`. For a fixed edge label `m`, the contributions whose test labels stay inside `m` have mean
  `∏_{p|m}v_p(2x+x²(1-2/p))`. A prime outside `m` must occur in **both** test labels and contributes `-x²/p²`, since the two residues cannot both be divisible by it. The total absolute size of all these outside-label contributions is at most the inside contribution times `exp(x²Σ_p1/p²)-1`. Truncation at degree `k` retains every inside contribution and only reduces this upper bound for the outside terms. Summing over `m` proves (11), with relative error `O_x((k+L)/H_0)` in the CRT mean and the finite-interval errors specified above.

  In particular, `x=√2-1` gives, for all the growing orders under consideration,

  \[
  \|B_k\|/E_k\geq(2-o(1))e^{-(3-2\sqrt2)L}.                  \tag{12}
  \]

  If `k∼cL`, the exponent in (11) is
  `L[c log(2x+x²)-x²]+o(L)`. At `k∼L`, the rational choice `x=4/5` already gives **growth** `exp((log(56/25)-16/25+o(1))L)`, not a saving.

Full-interval norms can be still larger on very rare high-divisor rows. If an interior `n` is divisible by `b≥k` pool primes, testing a point mass gives
`||B_k||≥√(2 binom(b,k))(1-1/H_0)^k`.
An interior multiple of a selected product exists if that product is shorter than the interior interval. All multiples of a particular selected product can be deleted at density `1/product+O(1/N)`. **None of the full-interval moment bounds is silently asserted to survive trimming.** The next argument handles trimming directly, without large moments or high-divisor exceptions.

## 4. A signed-row obstruction that survives arbitrary trimming

Here is an exact finite lemma. Put
`M=|h|max_{m∈M_k}m`, `I=(N+M,2N-M]∩Z`, and take any
`R⊂I` consisting of integers with **no pool-prime factors**. Let
`ρ=|R|/N`, `δ=|V\X|/N`, and `r=|R∩X|/N`. On every row of `R`,
`c_m(n)=(-1)^k/m`, for every `m`. Hence

\[
\begin{aligned}
 (-1)^k\langle1_{R\cap X},B_k|_X1_X\rangle
 &=2E_kr-\frac1N\sum_{m,\sigma}\frac1m
       |\{n\in R\cap X:n+\sigma hm\notin X\}|\\
 &\geq 2E_k(r-\delta).                                      \tag{13}
\end{aligned}
\]

The inequality uses only translation injectivity: for each `m,σ`, the lost set has at most `|V\X|` elements. No uncontrolled maximum degree enters. By Cauchy–Schwarz, if `ρ>2δ`,

\[
 \boxed{
 \frac{\|B_k|_X\|}{E_k}
 \geq\frac{2(r-\delta)}{\sqrt{r(1-\delta)}}
 \geq\frac{2(\rho-2\delta)}{\sqrt\rho}.}                       \tag{14}
\]

Thus `δ=o(ρ)` leaves a lower bound `(2-o(1))√ρ`. Conversely a proposed normalized bound `η` requires

\[
 \delta\geq\rho/2-\eta\sqrt\rho/4.                           \tag{15}
\]

(The same necessary inequality is automatic if `δ≥ρ/2`.) These statements are independent of `k`, factorial approximations, or any prime-pair assertion.

**Full-pool rough rows.** In the parameters of the question, let `R` contain every no-pool-factor integer in `I`. Then

\[
 \rho=(1+o(1))\prod_{p\in P}(1-1/p)=(1+o(1))e^{-L}.           \tag{16}
\]

An elementary sieve proof suffices here. Truncate inclusion–exclusion at adjacent orders `J,J+1`, with `J≈6L`. The Bonferroni gap is bounded by `L^J/J!+O(H^{J+1}/N)=o(e^{-L})`; the boundary loss is `O(M/N)=o(e^{-L})`. Finally `Σ1/p²≤L/H_0=o(1)`. This works because `L log H=o(log N)` and `k log H=o(log N)` in the stated regime. It is not an unjustified CRT average modulo the entire pool product.

For `L∼t/10`, `t=log log N`, (14) becomes

\[
 \|B_k|_X\|/E_k\geq(2-o(1))e^{-L/2}
       =(\log N)^{-1/20+o(1)}
\]

whenever `δ=o(e^{-L})`, in particular when `δ=o(1/log² N)`. To permit even `η≤1/log N`, (15) forces deletion of at least
`(1/2-o(1))e^{-L}N` vertices. This is far larger than the prime-pair benchmark `N/log² N`, before any additional CRT thinning. The relevant density is **pool-rough** `e^{-L}`, not the density `≈1/log N` of power-rough integers. Normalized `1_R` has `L^4` norm `ρ^(-1/4)=exp((1/4+o(1))L)`, so this obstruction is also compatible with an exponential-in-`L` fourth-norm allowance.

**Prime rows, without a pool-sieve asymptotic.** If `H<N` and `M=o(N)`, take `R` to be the primes in `I`. PNT gives `ρ∼1/log N`. Equation (14) proves (A) for every `δ=o(1/log N)`, hence for every exceptional set smaller than the prime-pair scale. This uses only a one-prime count, not primes at both endpoints. When `y<N`, this is also a zero-smooth-factor prime-cofactor test. Even outside the particular pool regime, this alone rules out the proposed normalized norm saving whenever these boundary hypotheses hold.

For comparison, `E_k≤e^L` always. In the displayed regime, `k≈t/log t` gives `log E_k=o(t)`, and `k∼cL` gives
`log E_k=c(1-log c)L+o(L)`. Already the full-interval trace/constant bound cannot reach `1/log N` there. Equations (13)–(16), unlike a trace argument, prove that tiny exceptional-set trimming cannot repair the failure. If many displacements exceed the interval, none of these interior conclusions is asserted: counting inactive edges in `E_k` would itself be an invalid amplification.

## 5. Scope, sources, and verification

* Proved: complete transport (2)–(3), the exact short-shift coefficient (4), triangular inversion (5), honest pinched transport and its Schur estimate (6)–(8), full-interval arithmetic norm tests (9)–(12), and the trimming-stable obstruction (13)–(16).
* Not proved or assumed: a prime-pair asymptotic, relative prime–rough Liouville cancellation, or same-row/CRT simultaneous occupancy. A lower bound for a uniform operator norm does not lower-bound the actual discrepancy for the particular arithmetic lifts. It rules out this **uniform-norm amplification**, not every possible function-specific arithmetic argument.
* The checked source `/corpus/src/2103.06853/trace.tex`, lines 186–265, proves the prime-displacement, order-one theorem. Lines 7505–7562 discuss composite lengths as a proposal, not a proved theorem for `B_k`. No power of that prime operator is identified with (2). There is no need to posit a missing composite spectral estimate: the requested estimate is contradicted by (14). For the changed pinched operator the actual available estimate is (7), whose insufficient norm budget is explicitly computed in (8).

`Submission/check_centered_composite_transport.py` performs exact rational finite checks of the masked transport and coefficient identities, triangular inversion, orthogonal/divisor-polynomial moments, the outside-label remainder estimate, the pinched blocks (including odd-shift vanishing), and the signed-row deletion inequality. Running `python3 Submission/check_centered_composite_transport.py` passed: 7 masked transport/coefficient cases, 2,303 residue-pattern inversions, 14 partition moments, 4 truncated count tests, pinching at `h=2,4,6`, and 24 deletion tests. These checks verify algebra, not asymptotic prime-pair statements; the counting arguments above supply the asymptotic proofs.

No Lean theorem or axiom was added. `Submission/Spec.lean` was not edited; its SHA-256 remains

```
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```
