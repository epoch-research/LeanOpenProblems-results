# Evans’s exact semiprime correlation: diagonal-extraction audit

## Result

**No proof or disproof of Erdős #5, and no new logarithmic consecutive-prime-gap construction, is obtained.** Evans proves a genuine **two-coordinate, exact-two-prime-factor** correlation, not merely separate information about the endpoints. The proposed extraction has an exact identity, and bounded coefficients on the *small* prime factor do survive the proof. What does not survive is a useful relative error for the extracted component.

The verified new inferences below are: the bounded-factor-weight extension with the source’s **absolute** error; a sign-flip obstruction to refining its rank-one main term; the exact factor-local Euler-product calculation; a positivity lower bound for the sign-averaged major-error intermediate quantity; and quantitative tests of narrowing and shift selection. No conjectural prime-pair asymptotic is used as a premise.

Source throughout: `/corpus/src/2102.12297/CorrelationsofAlmostPrimes.tex` (Evans), cited by **TeX line numbers and labels**. The earlier common-cofactor/HR audits are not repeated. `Submission/Spec.lean` was only read, not edited or used as a premise.

## 1. Exact extraction, including boundaries and off-diagonal terms

Let `I` be a finite set of odd primes, `R=max I`, `R²<X`, and `V=(X,2X]∩Z`. For `|h|<X`, set

\[
 A_h=\max(X,X-h),\quad B_h=\min(2X,2X-h),\quad
 J_h=(A_h,B_h]\cap\mathbb Z.
\]

Take either `a(r)=1_Prime(r)` or `a(r)=1_Prime(r) log r`, and define

\[
 f_p(n)=1_{p\mid n}a(n/p),\quad F_w(n)=\sum_{p\in I}w_pf_p(n),\quad
 C_w(h)=\sum_{n\in J_h}\overline{F_w(n)}F_w(n+h).
\]

A nonzero lift has a unique small factor: its other prime is `>R`. Write

\[
 N_{pq}(h)=\sum_{n\in J_h} f_p(n)f_q(n+h),\qquad
 C_w(h)=\sum_{p,q}\bar w_pw_qN_{pq}(h).                    \tag{1}
\]

For independent Rademacher signs `ε_p`, use the **same sign family at both endpoints**. For any coefficients `c_p`,

\[
\boxed{\mathbb E_\varepsilon C_{c\varepsilon}(h)
 =\sum_{\substack{p\in I\\p\mid h}}|c_p|^2
   \sum_{A_h/p<r\le B_h/p}a(r)a(r+h/p).}                  \tag{2}
\]

This is finite algebra: `E ε_p ε_q=1_{p=q}`, and the diagonal requires `p|h`. Equivalently, both `r,r+h/p` must lie in `(X/p,2X/p]`. For the source’s one-ended interval, replace this by just `X/p<r≤2X/p`. Clipping costs at most `O(|h|log²X)` in the log-weighted case when `|w_p|≤1`; for negative shifts the deleted strip is the *lower* strip. Uniqueness on the one-ended interval also needs `X-|h|>R²`. These boundary errors are negligible even against `X/p` in the polylogarithmic regime. See source **309–333**, `eq:correlationint`.

For `p≠q`, choose the unique `n_0∈[0,pq)` with `p|n_0`, `q|n_0+h`. Put `a_0=n_0/p`, `b_0=(n_0+h)/q`. Then, exactly,

\[
 n=n_0+pqt,\quad r=a_0+qt,\quad s=b_0+pt,\quad
 qb_0-pa_0=h,\quad A_h<n_0+pqt\le B_h.                    \tag{3}
\]

Thus the discarded terms are correlations of **different affine prime forms**, not the same cofactor pair. There is also a useful exact zero:

\[
 \boxed{p\ne q,\quad (p\mid h\text{ or }q\mid h)
        \quad\Longrightarrow\quad N_{pq}(h)=0.}           \tag{4}
\]

For example, if `p|h`, then `p|n+h=qs`; primality forces `s=p`, contradicting `n+h>X>R²`. Consequently deleting all factor labels dividing `h` deletes exactly the common-factor diagonal, with no mixed cross terms.

**Characters.** Factor weights `w_p=χ(p)` give

\[
 \frac1{\varphi(M)}\sum_{\chi\bmod M}\bar\chi(p)\chi(q)
 =1_{(pq,M)=1}\,1_{p\equiv q\pmod M}.                    \tag{5}
\]

This is exact extraction only if the labels are units and distinct modulo `M`; otherwise congruent off-diagonal labels remain. A prime `M>R` suffices. In particular, fewer than `|I|` unit residue classes cannot resolve `|I|` labels. The source’s characters multiply `n=pr`, not just `p`: averaging those characters is a different operation. An *external* character on `p` is a bounded coefficient covered below, even with large conductor; this does **not** enlarge the source’s major arcs or improve its errors.

## 2. What the actual proof permits

Write `L=log X`. From here on `C_w` and `D_c` use the **log-weighted** choice of `a`, unless an unweighted benchmark is explicitly stated. All shift estimates concern `0<|h|≤H`. In the small-polylogarithmic regime the source takes

\[
 P=L^B,\quad B=17+\varepsilon,\quad I=(P,P^{1+\delta}]\cap\mathbb P,
 \quad Q_0=L^{A'},\ A'=1+\varepsilon^2,\quad Q=PL,
\]

with `Bδ` sufficiently small. Theorem `thm:weightedmainthm`, **283–303**, is

\[
 \sum_{X<n\le2X}\varpi_2(n)\varpi_2(n+h)
 =X\mathfrak S(h)\lambda^2+O(XL^{-\eta}),\qquad
 \lambda=\sum_{p\in I}1/p,                               \tag{6}
\]

outside `O(HL^{-η})` shifts, for `L^(19+ε)≤H≤X L^(-A)`, `A>3` (with the specified `P` in the small-polylogarithmic subrange). Here `varpi_2(pr)=log r`, and only **some** `η(ε)>0` is supplied. The convention that `ε` may change from line to line is explicit at **179**; the repeated epsilons in the theorem and minor-arc hypotheses must not be read as an optimized numerical choice of `η`.

### Verified extension, not an assumption of uniform asymptotics

For each deterministic array `|w_p|≤1`, the same argument gives the following bound with constants independent of the array **when its parameter inequalities have positive slack**. A conservative explicit subrange is `0<ε<1` sufficiently small, `P=L^(17+ε)`, `H=L^D` for any fixed `D≥20+ε`, with `δ>0` sufficiently small in terms of `ε`. This avoids treating the printed reuse of epsilon as a proof of a borderline exponent: the displayed minor diagonal is `XP^(1+δ)L/H`, which at the literal choices `P=L^(17+ε), H=L^(19+ε)` has size `XL^(-1+Bδ)`, not `O(XL^(-1-η))`. The source states that epsilon may vary from line to line; this audit's derived weighted extension uses the explicit slackened subrange rather than that ambiguous borderline. Within that subrange,

\[
 C_w(h)=X\mathfrak S(h)|\lambda_w|^2+O(XL^{-\eta}),\qquad
 \lambda_w=\sum_{p\in I}w_p/p,                            \tag{7}
\]

outside `O(HL^{-η})` shifts, after decreasing `η` if needed. The exceptional set can depend on `w`. This includes signs, arbitrary sub-bins encoded by zero coefficients, and factor characters. Here is the check through the proof:

* **Minor arcs, 411–474:** insert `w_p` in the first factor of Cauchy–Schwarz at **417–419**. Its square norm only decreases. The enlarged sum over integer `m`, its nonnegativity, the geometric-sum cancellation, and the prime-pair **upper** sieve bound are unchanged.
* **Major main term, 500–540:** since `q≤Q_0<P`, both prime factors are units modulo `q`. Replace `λ` by `λ_w` in the principal-character approximation. PNT is applied to the unweighted *large* prime, separately for each `p`; bounded `w_p` preserves the absolute error. Thus `a_w(α)=μ(q)λ_w/φ(q) · Σ_{n∈V}e(βn)`.
* **Long-interval error `B_2`, 716–758:** the principal-character PNT and the Cauchy–Schwarz bound for the other characters remain valid with `|w_p|≤1`.
* **Short-interval error `B_1`:** in **1052–1132**, replace only `G_v` by `Σ w_pχ(p)p^{-s}`. The factorization lemma explicitly allows arbitrary coefficients (**888–905**); its remainder is dominated by the same positive semiprime coefficients. The small-`G` estimate **1165–1202** uses only its pointwise threshold and upper bounds for the untouched prime polynomial `H_v`.
* On the complement, Heath–Brown decomposes **only `H_v`** (**1207–1230**). Products of coefficients of `G_v^k` are bounded by the same factorial/convolution bounds (**1280–1344**); coefficients of `G_v^(2l)` have absolute value at most the same multinomial coefficient (**1440–1449**). The twisted fourth-moment lemma allows arbitrary coefficients (**1016–1025**). The prime-factored pointwise estimate at **1369** concerns the untouched long factor, not an arbitrarily weighted prime sum.

This verifies bounded **small-factor** weights. It does not verify arbitrary weights on the large prime, on `n`, or a CRT/interior mask.

### Averaging the estimates correctly

Do not union exponentially many weight-dependent exceptional sets. The source first proves the uniform minor-arc mean-square estimate (**376–399**)

\[
 \sum_{0<|h|\le H}|R_w(h)|^2\ll HX^2L^{-\kappa}.
\]

Jensen gives the same bound for `E_w R_w`. The singular-series exceptional set is independent of `w`, and the major-error bounds are uniform. Therefore, for `|c_p|≤1`, (2) really implies the **coarse additive estimate**

\[
 D_c(h):=\mathbb E C_{c\varepsilon}(h)
 =X\mathfrak S(h)\mu_c+O(XL^{-\eta}),\quad
 \mu_c=\sum_p|c_p|^2/p^2,                                \tag{8}
\]

outside the same order of exceptional shifts. This is not a relative asymptotic: its error is much larger than its displayed term. More samples of signs do not make the arithmetic error unbiased or independent.

## 3. The missing local terms and an exact precision obstruction

All following Euler-product statements are **local-density algebra**, not assertions of a prime-pair asymptotic. For the forms in (3), a prime `ℓ∉{p,q}` excludes one residue if `ℓ|h`, and two otherwise. At `ℓ=p` or `q`, it excludes one residue if that prime does not divide `h`, and *every* residue otherwise. Accordingly the formal weighted Hardy–Littlewood coefficient is

\[
 \begin{cases}
 \displaystyle \frac{\mathfrak S(h)}{pq}
       \frac{p-1}{p-2}\frac{q-1}{q-2},
       &p\ne q,\ (pq,h)=1,\\
 0,&p\ne q,\ (pq,h)>1,\\
 \mathfrak S(h/p)/p,&p=q,\ p\mid h,\\
 0,&p=q,\ p\nmid h.
 \end{cases}                                             \tag{9}
\]

Multiply by interval length `X-|h|` and by `bar w_p w_q`. The usual cofactor singular series occurs on the diagonal; for odd `p|h`,

\[
 \mathfrak S(h/p)=\mathfrak S(h)
 \begin{cases}(p-2)/(p-1),&p\nmid h/p,\\1,&p\mid h/p.\end{cases}
\]

For example, putting `b_p=(p-1)/(p(p-2))`, the whole formal coefficient is

\[
 \mathfrak S(h)\left(\left|\sum_{p\nmid h}w_pb_p\right|^2
              -\sum_{p\nmid h}|w_p|^2b_p^2\right)
 +\sum_{p\mid h}|w_p|^2\mathfrak S(h/p)/p.                 \tag{10}
\]

It differs from `S(h)|λ_w|²` by

\[
 O\!\left(\mathfrak S(h)\left[d_I(h)+\mu\right]\right),\quad
 d_I(h)=\sum_{p\in I,p\mid h}1/p,\quad \mu=\sum_{p\in I}1/p^2. \tag{11}
\]

Indeed `b_p-1/p=1/(p(p-2))`, so the change in the linear sum is at most `d_I(h)+O(μ)`, and the removed squared diagonal is `O(μ)`. In a fixed polylogarithmic shift range, `d_I(h)≤log H/(P log P)=O(1/P)`.

**Location in the source.** The major arcs have denominators `q≤Q_0<P` (**335–354**). No such denominator contains a pool prime. Their finite Ramanujan sum is at **591–627**; replacing it by `S(h)` uses the tail estimate **562–586**, with error and exceptions. That replacement does not manufacture the factor-resolved terms (9). In fact `S_p(a/p)=Σ_{X/p<r≤2X/p, r prime}log r ∼X/p`. These resonances have denominator `p`, hence lie outside the source’s major arcs. In the stated small-`δ` parameters `p<Q` as well. Terms of size (11) are invisible in the published error, not an unused positive main term already evaluated there.

### A proved obstruction, independent of any prime-pair conjecture

Fix `p∈I`, `p|h`, and let `w⁺` be all `+1`, while `w⁻` flips just the sign at `p`. By (4),

\[
 C_{w^+}(h)=C_{w^-}(h).
\]

But their proposed rank-one main terms in (7) differ by `4X S(h) λ_rest/p`, where `λ_rest=Σ_{q≠p}1/q`. Thus, for nonzero even `h`, **at least one** error satisfies

\[
 \boxed{\max_{\sigma=\pm}
 |C_{w^\sigma}(h)-X\mathfrak S(h)|\lambda_{w^\sigma}|^2|
 \ge 2X\mathfrak S(h)\lambda_{\rm rest}/p.}                \tag{12}
\]

So uniform accuracy `o(X/p)` with this main term on the required shifts is **false**, not merely unpublished. A refined main term must change.

Likewise `D_1(h)=0` exactly if no pool prime divides `h`, whereas (8) displays `X S(h) μ`. For `λ<1`, at least `(1-λ)H/2-O(1)` positive even shifts have no pool divisor: use `Σ_p floor(H/(2p))≤Hλ/2`. Hence even the sign-averaged rank-one main cannot have `o(Xμ)` error on almost all shifts. The minor arcs must supply its cancellation there.

### The target scale

For a common factor `p`, put `Y=X/p`, `k=h/p`. A target `k≈C log Y`, with fixed `C>0`, has formal main terms

\[
 \frac{X-|h|}{p}\mathfrak S(k)\quad\text{(log-weighted)},\qquad
 \mathfrak S(k)\int_{A_h/p}^{B_h/p}\frac{dt}{\log t\log(t+k)}
 \sim\frac{X\mathfrak S(k)}{p\log^2Y}\quad\text{(unweighted)}. \tag{13}
\]

These are benchmarks, **not proved asymptotics**. The corresponding **upper bounds**, up to a constant, are unconditional from the source’s sieve lemma **186–199**. Thus the source’s available error exceeds even the upper-bound scale of the desired component.

PNT/partial summation give

\[
 \lambda\sim\log(1+\delta),\qquad \mu\sim\frac1{P\log P}.
\]

A single diagonal has scale `X/p` against total scale `Xλ²`; its relative size is `asymp 1/p` for this fixed pool. For an `O(XL^{-η})` budget to be negligible against it, one needs `L^{-η}=o(S(k)/p)`. At `p≈L^b`, every fixed `η<b` fails by a power of `L`; uniform relative precision when `S(k)=O(1)` needs `η>b`. This is nowhere near a small surplus saving. Moreover the source’s two upper bounds in **186–199** give the unconditional inequality

\[
 \frac1H\sum_{0<h\le H}D_1(h)\ll X\sum_p\frac1{p^2}=X\mu:
\]

sum the single-`p` bound `D_p(pk)≪X S(k)/p` over `k≤H/p`, where `D_p` denotes that summand of (2). Thus averaging does not enlarge the diagonal scale. Its formal averaged benchmark is of that order, smaller still than `X/P`. Singular-series growth supplies no missing power of `L`.

## 4. Source-specific parameter and positivity tests

The exponents are traceable to actual inequalities, not just the theorem’s statement:

* The minor-arc diagonal is `XP^(1+δ)log(X/P)/H` (**430–434**). The final bound (**461–468**) is
  \[
  I_{\rm minor}\ll XP^\delta\left[L^{o(1)}
       (Q_0^{-1}+P^{-1}+Q/H)+PL/H\right].                \tag{14}
  \]
  To get `X/L^(1+κ)` requires roughly `H>P L²` and `A'>1`. This is the additional two logarithmic powers behind **19**, with small surpluses reallocated as in the source’s epsilon convention.
* For the major error, `U=Q_0^(1+ε²)` (**1063**), `α_1=3/34-ε'` (**1140–1147**), and `α_2=2/17-ε'` (**1241**). The small-`G` bound (**1194–1202**) requires
  \[
  \kappa_B<2\alpha_1B-(3+2\varepsilon^2)A'-B\delta.       \tag{15}
  \]
  At leading exponents `2(3/34)·17=3`; the Type-II factorial condition (**1320–1344**) also requires `B>1/[2(α_2-α_1)]=17`.
* The remainder bound `1/(U L²)` at **1124–1132** supplies only a surplus exponent below `A'ε²` when compared with `1/(Q_0 L^(2+κ_B))`. The `Q_0` term of (14) similarly gives only `κ<A'-1-Bδ`. The major `AB` estimate (**536–540**) and Chebyshev (**397–399**) further reduce exponents; they do not amplify them.

Thus the displayed proof certifies small surplus savings, nowhere near the diagonal requirement. The remark **305–307** about arbitrary logarithmic accuracy explicitly changes the dependencies of `H,P` and the circle-method parameters. It does not allow arbitrary accuracy at `P=L^(17+ε), H=L^(19+ε)`. Even simply raising these parameters while retaining the displayed small-`G` argument gives a saving in (15) smaller than `2α_1B<B`, before the later losses. This is an obstruction to that *estimate chain*, not a claim that 17 or 19 is an intrinsic arithmetic barrier for every possible method.

### Random signs do not remove the positive short-interval error

There is a further unconditional test of the source’s **actual `B_1` reduction**, not just of its reported bound. Let `y=Q/2=PL/2`, `z=Δ/2`, with `Δ=X^.97` as in **646–651**, and

\[
 A_{p,y}(x)=\frac1y\sum_{x<pr\le x+y}\log r.
\]

On averaging independent signs, the `q=1` contribution to `B_1` becomes the sum over `p` of the squared short-minus-long discrepancies. The source’s long-interval PNT (**723–737**) gives `A_{p,z}(x)=(1+o(1))/p`, uniformly. Also

\[
 \int_X^{2X} A_{p,y}(x)\,dx=(1+o(1))X/p,\qquad
 \int_X^{2X} A_{p,y}(x)^2\,dx
 \ge(1-o(1))\frac{XL}{py}.                              \tag{16}
\]

For the inequality retain just identical-prime terms in the nonnegative square, with `X+y<pr≤2X`; each has integration length `y`. PNT supplies the sum of `log²r`. End strips are negligible. The integer-count centering in `B_1` differs from exact constant centering by `O(1/(py))`, also negligible. Expanding the square now proves

\[
 \boxed{\mathbb E B_1(X)
 \ge(2-o(1))\frac{X\lambda}{P}-(1+o(1))X\mu
 \gg \frac{X\lambda}{P}.}                              \tag{17}
\]

For weights `c_p ε_p`, replace `λ` by `Σ|c_p|²/p` and `μ` by `μ_c`; since every `p>P`, the lower bound is at least `(1-o(1))Xμ_c`. Thus averaging signs cannot make this positive-energy intermediate quantity `o(Xμ_c)` at the source’s `Q`. For the full pool its lower bound is larger by order `log P` than the averaged diagonal benchmark. This uses only a one-prime PNT and positivity, not a prime-pair lower bound.

**Scope:** (17) lower-bounds `E B_1`, not `B²=∫_M|b|²`, and not a particular Fourier coefficient. The source uses `B²≪B_1+B_2` (**655–701**). Therefore trying to prove a sufficiently tiny upper bound by this positive-energy route fails; a different oscillatory treatment is not ruled out by (17).

## 5. Narrow bins, selected shifts, and amplification

**Gap geometry and exceptional shifts.** At the printed lower endpoint `H=L^(19+ε)`, a factor near `H/L=L^(18+ε)` is outside the allowed pool when `Bδ<1`. For `h≈H` the divided gaps are at least order `L^(2-Bδ)`, not `L`. One may instead select smaller `h`, but this must be tested against the exceptions. For a fixed target band `k/log(X/p)∈[C-τ,C+τ]`, `0<τ<C`, the number of possible shifts is at most

\[
 O\!\left(L\,\#I\right)
 =O\!\left(\frac{P^{1+\delta}L}{\log P}\right),\qquad
 \frac{\#\text{target shifts}}H
 \ll \frac{L^{-1+B\delta}}{\log P}.                      \tag{18}
\]

The small certified exception exponent can swallow *all* these shifts. This is an absence of a guarantee, not an assertion that the actual exceptional set does swallow them.

**Many factors of `h` cannot amplify this target.** Always `ω_I(h)≤log|h|/log P`; at the lower endpoint `H<P²`, it is at most one. More strongly, if `h=pk` and `0<|k|<P`, any other `q∈I` dividing `h` would divide `k`, which is impossible. Also `p²∤h`. Thus at a logarithmic cofactor gap there is **exactly one** pool divisor, independently of how large an ambient `H` one chooses. Small factors *outside* the pool change the singular series, not the diagonal multiplicity; `S(h)≪log log(3|h|)` (source **453**) gives only iterated-log gains in this regime.

**Narrowing really can change one scale loss, but not for free.** Let `J⊂(R,2R]` contain `m` primes. Then

\[
 \lambda_J\asymp m/R,\quad \mu_J\asymp m/R^2,\quad
 \mu_J/\lambda_J^2\asymp1/m.                             \tag{19}
\]

For a shift with one `J` divisor, the diagonal benchmark is `X/R`, versus coherent main scale `Xm²/R²`; their ratio is `asymp R/m²`. Thus it would be wrong to claim an unavoidable `1/R` pointwise loss for *every* bin: taking `m≈√R` makes these scales comparable. But the shifts with any `J` divisor have density at most `Σ_{p∈J}1/p≈m/R`. At `m≤√R`, that is at most `R^(-1/2)`, far below the source’s exception allowance (`R=L^b`, `b≈17`, versus its small certified `η`). The absolute bound inherited from (7) is not a bound relative to `λ_J²`.

Narrowing may improve some Cauchy–Schwarz constants if the proof is reworked. It does not alter (2), (4), (9), or the density just calculated. In the extreme `m=1`, the resolved correlation is **exactly a prime-pair correlation** at scale `X/p`, supported on `p|h`. A relative estimate there is the required prime-pair estimate itself, not a semiprime corollary bypassing it.

**Divisibility-supported `h` weights do not rescale the error or exceptions.** A fixed `p` has only `O(H/p)` eligible shifts, all potentially exceptional. For a set of `M` selected shifts, the available mean-square bound gives only

\[
 \sum_{h\in\mathcal A}|R(h)|\ll X\sqrt{HM}\,L^{-\kappa/2}, \tag{20}
\]

not `MX L^(-κ/2)`. More generally use the `l²` norm of the shift weight. Choosing factor weights *depending on `h`* is not covered by a weight-independent common good set. The Jensen argument proving (8) is legitimate but gives no extra saving.

Exactly, after selecting `h=pk`, any weighted sum of the isolated terms is

\[
 \sum_{p,k}v_{p,k}\sum_{r:\,pr,p(r+k)\in V}a(r)a(r+k).    \tag{21}
\]

Its evaluation in a logarithmic `k` band is an averaged prime-pair problem. Equivalently `S_p(α)=T_p(pα)`; Fourier weighting on `p|h` exposes the `a/p` resonances excluded from the old major arcs. It cannot be evaluated by just retaining the old rank-one term. Nonnegative/Fejér averaging can give coarse short-interval pair lower bounds from first moments, but it includes the zero-shift self-pair contribution, of the same order at logarithmic length, and supplies neither an arbitrary prescribed annulus nor absence of interior primes. Precisely, a nonzero nonnegative trigonometric kernel cannot have its zero-shift coefficient zero: its integral would be zero. So annulus-only weights cannot use that positivity argument without extra estimates. The source uses positivity here for **upper** bounds (e.g. **443–448**, **1181–1185**), not a hidden lower bound for (21).

## 6. Global consecutivity is still a separate missing condition

Even a positive term in (2) gives only two primes. For `k>0`, the exact consecutive-prime count inserts

\[
 M_k(r)=\prod_{1\le j<k}(1-1_{\mathbb P}(r+j))
\]

inside the inner sum in (2). This is not a factor-only coefficient `w_p`. A CRT mask forcing these intervening integers to be composite similarly changes the **large-cofactor** prime sums; the unweighted prime-factored/character estimates used above cannot simply be reused. Multiplication by `p` already makes the lifted integers composite and says nothing about intervening primes between the cofactors.

Finite example: in `V=(300,600]`, `303=3·101` and `339=3·113` give a common-factor term at `h=36`, but `103,107,109` lie strictly between the cofactors. So the original full-gap conjecture requires a masked two-prime assertion beyond even the unresolved relative diagonal estimate.

## 7. Verification and source scope

`python3 Submission/check_semiprime_diagonal_extraction.py` passed, using only integer and rational arithmetic:

* 480 extraction/mask/boundary cases and 2,880 CRT off-diagonal checks;
* 58 exact character kernels, including a surviving small-modulus collision;
* 720 finite Euler-factor checks for (9), **not** tests of a prime-pair asymptotic;
* 70 support/bin checks and 5 exact periodic versions of the variance inequality (16);
* the explicit nonconsecutive cofactor pair above.

The argument for (17), rather than the finite test, supplies its asymptotic proof. The same script checks the sign-flip rigidity inequality, the two `17` balances, and positive small surplus exponents in (14)–(15). Relevant remaining source locations: `thm:mainthm` **39–52**; singular series **21–25**; `B_1`/Dirichlet-polynomial bound **764–841**, completion **1488–1513**. The other theorems do not supply the missing range: typical `E''_2` requires `H≥exp((log X)^(1-o(1)))` (**64–70**, parameters **1519–1523**); prime–`E''_2` requires `H≥X^(1/6+ε)` (**74–79**).

No Lean theorem or axiom was added. `Submission/Spec.lean` retains SHA-256

```
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```
