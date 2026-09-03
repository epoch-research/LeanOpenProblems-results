# Erdős 66: rigorous constraints, not a solution

## Outcome and formal scope

No proof of existence or nonexistence was obtained. In particular, the arguments below do **not** upgrade a square-root-logarithmic obstruction to a logarithmic one.

`Submission/Constraints.lean` is independent of `Submission/Spec.lean` and uses the actual `AdditiveCombinatorics.sumRep` definition. It kernel-checks positivity of a nonzero limit, eventual positivity of the representation function, infinitude of the set, and both parity formulas below. Its reported axiom dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. The analytic consequences in this note are mathematical proofs, not Lean-formalized theorems. `Spec.lean` was not edited.

## Notation and hypothesis

Write

- `a_n = 1_A(n)`;
- `r(n) = sum_{j=0}^n a_j a_{n-j}`, with **ordered** pairs;
- `A(x) = #{a in A : a <= x}`;
- `ell_0 = ell_1 = 0`, `ell_n = log n` for `n >= 2`;
- `e_n = r(n) - c ell_n`.

Assume `c != 0` and `r(n)/log n -> c`. Since the quotient is nonnegative for `n >= 2`, `c > 0`. The hypothesis is precisely `e_n = o(log n)`. In particular `r(n) > 0` eventually and `A` is infinite.

For `|z| < 1`, put

\[
 F(z)=\sum_{n\ge0}a_nz^n,\quad
 G(z)=c\sum_{n\ge0}\ell_nz^n,\quad
 E(z)=\sum_{n\ge0}e_nz^n.
\]

All series converge absolutely, and `F(z)^2 = G(z)+E(z)`.

## 1. The forced counting asymptotic

The elementary Abelian asymptotic is

\[
 \sum_{n\ge2}\log n\,e^{-tn}
 \sim t^{-1}\log(1/t) \qquad(t\downarrow0).
\]

For example, write `log n = log(1/t)+log(tn)`: `t sum exp(-tn) -> 1`, and the Riemann sums `t sum log(tn) exp(-tn)` remain bounded (indeed, converge to the finite integral of `log u exp(-u)`). The logarithmic singularity at zero is integrable, and exponential decay controls the other endpoint.

Also `sum |e_n| exp(-tn) = o(t^{-1} log(1/t))`: for any positive epsilon, bound the tail by `epsilon sum ell_n exp(-tn)` and treat the finite initial segment separately. Consequently

\[
 F(e^{-t})^2\sim \frac c t\log(1/t),\qquad
 F(e^{-t})\sim\sqrt c\,t^{-1/2}\sqrt{\log(1/t)}.
\]

Apply the nonnegative-coefficient Karamata Tauberian theorem: if `u_n >= 0` and `sum u_n exp(-tn) ~ C t^{-alpha} L(1/t)` for slowly varying `L` and `alpha > 0`, then `sum_{n<=x}u_n ~ C x^alpha L(x)/Gamma(alpha+1)`. Here all its hypotheses hold with `alpha = 1/2` and `L(x)=sqrt(log x)`. Thus

\[
 \boxed{A(x)\sim\frac{2\sqrt c}{\sqrt\pi}\sqrt{x\log x}.}
\]

This is a statement about partial sums of the indicator, **not** a pointwise asymptotic for `a_n`.

## 2. Fixed-modulus equidistribution

For every fixed `q >= 1` and residue `j`, necessarily

\[
 \boxed{\#\{a\le x:a\in A,\ a\equiv j\pmod q\}
       \sim \frac{A(x)}q.}
\]

Here is the generating-function proof, including the cancellation estimate. Write `rho -> 1-`, `delta=1-rho`. For any fixed unit complex number `zeta != 1`,

\[
 (1-z)\sum\ell_nz^n
   =\sum_{n\ge2}\log\frac n{n-1}\,z^n.
\]

Since `log(n/(n-1)) <= 1/(n-1)`, the absolute value of the series on the right, on `|z|=rho`, is at most `-rho log(1-rho)`. Therefore

\[
 |G(\rho\zeta)|=O_\zeta(\log(1/\delta)).
\]

Meanwhile

\[
 |E(\rho\zeta)|\le\sum |e_n|\rho^n
       =o(\delta^{-1}\log(1/\delta)).
\]

Because `|F(z)|^2=|F(z)^2|`, these imply

\[
 F(\rho\zeta)=o(F(\rho)).
\]

This holds for every fixed nontrivial character, not just roots of unity. For the `q`th roots of unity, finite Fourier inversion gives

\[
 \sum_{n\equiv j\ (q)}a_n\rho^n
   =\frac1q\sum_{k=0}^{q-1}\zeta^{-jk}F(\rho\zeta^k)
   \sim \frac1q F(\rho).
\]

The series on the left has nonnegative coefficients, so the same Tauberian theorem gives the displayed counting assertion. There is no justified uniformity here for a modulus growing with `x`; neither exact equality nor a rationality condition on `c` follows.

## 3. A quantitative mean-square obstruction

One can derive the following directly, without quoting a strengthened Erdős–Fuchs theorem:

\[
 \boxed{\liminf_{t\downarrow0}
  \frac{t}{\log(1/t)}\sum_{n\ge0}e_n^2e^{-tn}\ \ge c.}
 \tag{MS}
\]

Use normalized circle measure `dtheta/(2 pi)`. First, the difference-series identity from the previous section gives

\[
 \|G(\rho e^{i\theta})\|_{L^1}
       =O_c\!\left(\log^2\frac1{1-\rho}\right).
\]

Indeed, its numerator is `O(log(1/(1-rho)))`, and the integral of `1/|1-rho exp(i theta)|` is also `O(log(1/(1-rho)))`, by `|1-rho exp(i theta)|` comparable to `sqrt((1-rho)^2+theta^2)` for `rho >= 1/2` and `|theta| <= pi`.

The crucial use of the set condition is `a_n^2=a_n`. Parseval, followed by the triangle inequality and Cauchy–Schwarz, gives

\[
 \begin{aligned}
 F(\rho^2)
 &=\int |F(\rho e^{i\theta})|^2\,\frac{d\theta}{2\pi}\\
 &=\|F(\rho e^{i\theta})^2\|_{L^1}\\
 &\le \|G(\rho e^{i\theta})\|_{L^1}
       +\|E(\rho e^{i\theta})\|_{L^1}\\
 &\le O_c\!\left(\log^2\frac1{1-\rho}\right)
       +\left(\sum e_n^2\rho^{2n}\right)^{1/2}.
 \end{aligned}
\]

Set `rho=exp(-t/2)`. The first section gives

\[
 F(\rho^2)\sim\sqrt{c\,t^{-1}\log(1/t)}.
\]

The `O(log^2(1/t))` term is little-o of this quantity. Subtract it and square (the difference is positive for small enough `t`) to prove (MS).

In particular,

\[
 \boxed{\limsup_{n\to\infty}
   \frac{|r(n)-c\log n|}{\sqrt{\log n}}\ge\sqrt c.}
 \tag{P}
\]

If this failed, for some `K < sqrt(c)` one would have `e_n^2 <= K^2 log n` eventually. Abel summation of this inequality would contradict (MS). No conclusion about the **sign** of these errors is claimed.

The precise remaining gap is important. The proposed limit gives only

\[
 \sum e_n^2e^{-tn}=o\big(t^{-1}\log^2(1/t)\big),
\]

whereas (MS) gives a lower bound of order `t^{-1} log(1/t)`. These estimates are compatible. For example, the error magnitude `(log n)^{3/4}` is both little-o of `log n` and much larger than `sqrt(log n)`.

Also (MS) does not by itself assert a lower bound with the same constant for every unweighted partial sum. It implies a limsup obstruction for such partial sums; an unwarranted Tauberian upgrade would be a further gap.

## 4. Parity and forced downward variation

The exact identities, both kernel-checked in `Constraints.lean`, are

\[
 r(2m)\equiv 1_A(m)\pmod2,\qquad r(2m+1)\equiv0\pmod2.
\]

They follow by pairing every off-diagonal ordered pair with its swap. Thus

\[
 \#\{n\le x:r(n)\text{ is odd}\}=A(\lfloor x/2\rfloor)
 \sim\sqrt{\frac{2c}\pi}\sqrt{x\log x}.
\]

In particular the odd-valued representation counts are infinite but have density zero. This is compatible with a logarithmic asymptotic; approximating a real number by an even or odd integer costs only a bounded error.

There is a somewhat stronger local consequence. Define

\[
 V(X)=\sum_{n=1}^{\lfloor X\rfloor}|r(n)-r(n-1)|,
 \quad
 D(X)=\sum_{n=1}^{\lfloor X\rfloor}\max(r(n-1)-r(n),0).
\]

For every positive `a in A`, both neighbors of `r(2a)` are even and `r(2a)` is odd. Hence both adjacent absolute differences are at least one. The edges associated to different `a` are distinct. Therefore

\[
 V(2N+1)\ge2\big(A(N)-1_A(0)\big).
\]

For any real sequence, telescoping gives

\[
 D(X)=\frac{V(X)-r(\lfloor X\rfloor)+r(0)}2.
\]

Under the hypothetical limit it follows that

\[
 \boxed{D(2N+1)\ge A(N)-O(\log N).}
\]

Thus the representation function cannot be eventually nondecreasing, and its cumulative downward variation has order at least `sqrt(N log N)`.

One can also count decreases. Let `J(X)=#{1<=n<=X:r(n)<r(n-1)}`. The limit implies

\[
 M(X):=\max_{1\le n\le X}|r(n)-r(n-1)|=o(\log X).
\]

To see this, use `e_n=o(log n)`, split off finitely many initial indices, and bound the remaining differences by `2 epsilon log X + O(1)`. Since `D(X)<=J(X)M(X)`, the preceding lower bound entails

\[
 J(X)=\omega\!\left(\sqrt{X/\log X}\right).
\]

These local oscillations still do not force deviations of size comparable to `log n` from the proposed main term.

## 5. Relevant corpus results and their actual scales

The directly relevant source is Csaba Sándor, *Additive representation functions and discrete convolutions*, arXiv:2009.03392:

- `/corpus/src/2009.03392/2009.03392.tex`, lines 134–140: the quoted Erdős–Sárközy 1986 obstruction is `max_{n<=N}|F(n)-R_A(n)| = o(sqrt(F(N)))` for suitable increasing `F`. At `F(n)=c log n`, this excludes square-root-logarithmic error, not the requested little-o-logarithmic error.
- Lines 157–170 (source label `thm4`): a discrete-convolution generalization excludes `R_A(n)=(b*b)(n)+o(sqrt((b*b)(n)))`, under `0<=b_n<=1`, `limsup b_n<1`, and `(b*b)(n)->infinity`.
- Lines 420–455: its proof uses Parseval and the idempotence of indicator coefficients; the explicit argument in Section 3 retains a quantitative constant for the logarithmic target.
- Lines 186–192 (source label `thm6`): the existence theorem gives error of order `sqrt(log n * (b*b)(n))`. At logarithmic size this is `O(log n)`, not `o(log n)`. The source states a numerical constant 5 here while its final proof displays 8; only the order of magnitude is used in this report.
- Lines 37–47: Bateman's summatory extension excludes an error `o(G(N)^{1/4}/sqrt(log N))`. For `G(N)~c N log N`, this is `o(N^{1/4}/(log N)^{1/4})`.

Dai–Pan, *On the Erdős–Fuchs theorem*, arXiv:1608.08433, `/corpus/src/1608.08433/1608.08433.tex`, lines 50–63, records the classical summatory obstruction and the improvement removing its logarithmic factor for a linear main term. It does not provide the missing pointwise logarithmic obstruction.

The target hypothesis implies only

\[
 \sum_{n\le N}r(n)=c\sum_{n\le N}\log n+o(N\log N).
\]

It supplies no summatory remainder remotely as small as these forbidden scales. Subtracting a smooth main term does not turn the error sequence into another set's representation function.

External web access failed (DNS), so this is a local-corpus investigation, not a claim to have exhaustively checked current literature.

## 6. Other pitfalls checked

- **Ordinary versus ordered representations:** the present `sumRep` is the full ordered count. An unordered convention changes the leading constant by a factor two; it does not change existence of a nonzero logarithmic limit.
- **Taking discrete derivatives of an asymptotic:** `r(n)~c log n` implies `r(n+1)-r(n)=o(log n)`, not convergence of the differences to zero. Integrality cannot be used to make the representation function eventually constant.
- **Fractional square roots:** the real-axis generating-function asymptotic permits a square-root singularity at `z=1`; such a boundary singularity is not incompatible with a power series analytic inside the unit disk.
- **Natural boundaries:** even a bounded-coefficient error series can have a natural boundary, for example `sum z^{k!}`. Thus coefficient errors `o(log n)` do not force analytic continuation away from `z=1`.
- **Fixed moduli:** fixed-modulus equidistribution is neither exact equality of counts nor uniformity for moduli that grow with `x`. It does not force `c` to be rational, integral, or zero.
- **Random-model concentration:** Bernoulli selection with `p_n` asymptotic to `sqrt(c/pi) sqrt(log n/n)` has expected ordered representation count asymptotic to `c log n` and variance of order `log n`. Fixed-`n` relative concentration therefore is plausible and provable, but it is not an almost-sure assertion for all sufficiently large `n`. The usual union-bound/Chernoff route needs an extra logarithmic factor in the variance scale. Failure of that sufficient summability test is not, by itself, a proof of nonexistence.
- **Signed or unrestricted-integer constructions:** inverse representation theorems on the full group of integers do not establish a set of nonnegative integers with the requested convolution.

## Remaining obstacle

A negative solution requires a genuinely stronger argument: for every candidate and every `c>0`, errors of magnitude comparable to `log n` must occur infinitely often (or an equivalent contradiction must be obtained). The verified consequences above allow errors between square-root-logarithmic and logarithmic size and therefore do not settle Erdős 66.
