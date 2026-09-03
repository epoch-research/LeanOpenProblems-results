# Direct odd count in the 0.6 / 0.9 prime rectangle: independent audit

## Verdict and scope

**The three quantitative auxiliary estimates are valid with the qualifications below. They do not prove the target assertion.** In particular, none of the arguments controls the entire signed count by a power smaller than one.

1. The coefficient `-2/(p-1)` and the restriction to odd characters are exact for a **centered-weight sum** `D_0`, not literally for `D`. There is a proved `D-D_0 = O(1)` error. The proof of this error below uses Brun–Titchmarsh; bare congruence counting would leave a logarithmic loss. The exact character expansion of `D` has additional even-character terms.
2. The quadratic second-moment estimate needs a factor `||beta||_infinity^2`, or the hypothesis `|beta_b| << 1`. With this understood, the real-odd-character contribution is `O(X^(19/20) log X)`. The same bound holds for the real-odd portion of the exact, uncentered character expansion.
3. With the specified Fourier convention, the kernel in the question has the **positive factor `+4`**, and the outer normalization is `H^(-1)`. The ordinary large-sieve estimate, including its factor `P^(-1)`, is valid. The short-frequency bound is
   \[
   |D_{\le R}|\ll X^{7/20}R^{3/2}(\log X)^{3/2}\qquad(1\le R\le H).
   \]
   Thus `R = X^(2/5)` gives `O(X^(19/20) (log X)^(3/2))`.
4. The circle identity has the stated sign `-2i`. The stated small-denominator noncentral arcs have rapid decay, and the central arc contributes `O(1)`. “Noncentral” must mean a noninteger center on the circle: for example, `1 <= c < r`, `(c,r)=1`, so `r >= 2`. Merely writing `c != 0` without specifying representatives is insufficient: `c=r=1` is central and violates the proposed distance lower bound.

All primes remain primes throughout. Only `a,b` run over unrestricted positive integers. No prime-power replacement for `p` is being made. No file named Spec was used for this audit.

The accompanying `DirectOddCountVerification.py` performs exact finite algebraic checks, using rational arithmetic and cyclotomic polynomial quotients, together with exact exponent arithmetic. It is a regression check of identities and normalizations, **not numerical evidence for asymptotic estimates or a formal proof of the target**. The main agent should independently review this note and the script.

## 1. Conventions, scales, and classical input

Let `X` tend to infinity, and put
\[
 A=X^{2/5},\quad B=X^{1/10},\quad P=X^{3/5},\quad
 Q=X^{9/10},\quad H=X^{1/2}.
\]
The useful exact identities are
\[
 AP=BQ=X,\qquad P/B=H,\qquad AB=H.
\]
Let `U,V,W,Z` be fixed real functions in `C_c^infinity((1,2))`, extended by zero to the real line. Constants may depend on these functions and finitely many of their derivatives; they are not claimed to be uniform over arbitrary `X`-dependent weights. Write `e(t)=exp(2 pi i t)` and
\[
 \widehat f(\xi)=\int_{\mathbb R}f(y)e(-\xi y)\,dy.
\]
The signed count is
\[
 D=\sum_{\substack{a,b\ge1\\p,q\ {\rm prime}}}
 U(a/A)V(b/B)W(p/P)Z(q/Q)\log p\log q
 \bigl(1_{ap-bq=1}-1_{ap-bq=-1}\bigr).
\]
Here and below, `p ~ P` means `P < p < 2P`, and similarly for other variables; support restrictions can only shorten these intervals.

Take `X` sufficiently large that `2B<P`, `2P<Q`, and `P>2`. Then all contributing `p` are odd, `p` does not divide `b`, and `p != q`. In particular, the inverse of `q` modulo `p` is always defined. These are asymptotic statements; for smaller `X`, the inverse-residue formula would have to omit `p=q` explicitly.

We use the following classical unconditional facts:

* Chebyshev's bound `theta(T)=sum_{ell<=T, ell prime} log ell << T`. Consequently,
  \[
   \#\{p\sim P\}\ll P/\log P,\qquad
   \sum_{q\sim Q}(\log q)^2\ll Q\log Q.
  \]
* Brun–Titchmarsh in the form
  \[
   \pi(T;m,a)\le {2T\over\varphi(m)\log(T/m)}
   \quad(T>m,\ (a,m)=1).
  \]
  Its use is only an upper-bound sieve use, not a prime equidistribution asymptotic.
* Smooth Poisson summation, Fourier/Mellin inversion, elementary character orthogonality, and quadratic reciprocity.

For clarity, the needed large-sieve inequalities are proved below, up to absolute constants, rather than being invoked with implicit normalizations. No new proof of Chebyshev or Brun–Titchmarsh is claimed.

## 2. Eliminate `a`, and account for the missing shift

For fixed `p,b,q`, set
\[
 t={bq\over pA},\qquad \epsilon_p={1\over pA}.
\]
Eliminating `a` gives the exact identity
\[
 D=\sum_{p,b,q} W(p/P)V(b/B)Z(q/Q)\log p\log q
 \left[
 U(t+\epsilon_p)1_{bq\equiv-1\ (p)}
 -U(t-\epsilon_p)1_{bq\equiv1\ (p)}
 \right].                                                \tag{2.1}
\]
All integer and support restrictions are respected by the zero extension of `U`.
Define the centered sum
\[
 D_0=\sum_{p,b,q} W(p/P)V(b/B)Z(q/Q)\log p\log q\,
 U(t)\left[1_{bq\equiv-1\ (p)}-1_{bq\equiv1\ (p)}\right]. \tag{2.2}
\]

### Centering error

The mean value theorem bounds either change in `U` by `C/(pA)`. For either of the two nonzero residue classes `q == +/- inverse(b) (mod p)`, Brun–Titchmarsh gives, uniformly in `p ~ P` and the residue,
\[
 \sum_{\substack{q\sim Q\ {\rm prime}\\q\equiv a\ (p)}}\log q
 \ll {Q\log(2Q)\over(p-1)\log(2Q/p)}\ll {Q\over p}.       \tag{2.3}
\]
Indeed, `log(2Q/p)` is comparable to `(3/10) log X`, whereas `log Q=(9/10) log X`.
It follows that
\[
 |D-D_0|
 \ll {BQ\over A}\sum_{p\sim P}{\log p\over p^2}
 \ll {BQ\over AP}=1.                                    \tag{2.4}
\]
This proves the `O(1)` error in the Fourier formula as well as the legitimacy of using the centered character coefficient. Smoothness of the zero extension handles support boundaries; no sharp-support error has been omitted.

### Exact versus centered character expansions

For a prime `p`, characters are extended by zero on multiples of `p`. Orthogonality gives
\[
 1_{n\equiv-1\ (p)}-1_{n\equiv1\ (p)}
 =-{2\over p-1}\sum_{\chi\ ({\rm mod}\ p),\ \chi(-1)=-1}\chi(n).
                                                               \tag{2.5}
\]
Thus the proposed coefficient, with no complex conjugation needed at `+/-1`, gives exactly
\[
 D_0=-2\sum_{p\sim P}{W(p/P)\log p\over p-1}
 \sum_{\chi(-1)=-1}
 \sum_{b,q}V(b/B)Z(q/Q)U\left({bq\over pA}\right)
              \log q\,\chi(bq).                         \tag{2.6}
\]
The sign is negative: `ap-bq=+1` corresponds to `bq == -1 (mod p)`.

For the exact sum `D`, the coefficient inside the character expansion is instead
\[
 {1\over p-1}
 \bigl[\chi(-1)U(t+\epsilon_p)-U(t-\epsilon_p)\bigr]\chi(bq).
                                                               \tag{2.7}
\]
For odd characters its bracket is `-U(t+epsilon_p)-U(t-epsilon_p)`; for even characters it is `U(t+epsilon_p)-U(t-epsilon_p)`. Therefore even characters do not disappear identically from the uncentered expansion. Equation (2.4), not an unsupported omission of those terms, relates the two full expansions.

## 3. Audit of the real-odd-character estimate

### 3.1 Elementary quadratic second moment

For complex numbers `beta_b` supported in `B < b < 2B`,
\[
 \sum_{p\sim P\ {\rm prime}}
 \left|\sum_b\beta_b\left({b\over p}\right)\right|^2
 \ll \|\beta\|_\infty^2
       \left(PB\log(2B)+B^4\right).                      \tag{3.1}
\]
Here `P,B >= 2` suffice; our application has much larger `P`.

**Proof.** Nonnegativity allows extension of the outer sum to all odd positive integers `r` in `(P,2P)`, with the Jacobi symbol in place of the Legendre symbol. Expansion then gives
\[
 \sum_{b,b'}\beta_b\overline{\beta_{b'}}
 \sum_{\substack{P<r<2P\\r\ {\rm odd}}}
       \left({bb'\over r}\right).                       \tag{3.2}
\]
For a positive integer `n`, extend `r -> (n/r)` by zero at even `r`. Quadratic reciprocity shows this is a Dirichlet character modulo `8n`, possibly imprimitive: on odd units its factors depend only on `r` modulo `8` and the odd prime factors of `n`, and it is zero precisely off the units modulo `8n`.

Here is an explicit check of nonprincipality when `n` is not a square. Factor `n=2^v product_ell ell^(e_ell)` over odd primes `ell`. If some odd `ell` has odd exponent, choose `r == 1 (mod 8)`, choose a quadratic nonresidue modulo that `ell`, and choose `r == 1` modulo all other odd prime factors of `n`. The Chinese remainder theorem gives a unit modulo `8n`, and reciprocity gives `(n/r)=-1`. If no odd prime has odd exponent, then `v` is odd; choose instead `r == 5 (mod 8)` and `r == 1` modulo every odd prime factor. Again `(n/r)=-1`. Multiplication by this unit permutes the complete residue system and negates its character sum. Thus the complete sum modulo `8n` is zero, and an arbitrary interval sum has absolute value at most `8n`.

For nonsquare `bb'`, this is `O(B^2)` per pair, and there are `O(B^2)` pairs, giving `O(||beta||_infinity^2 B^4)`.

For square `bb'`, the Jacobi symbol is `0` or `1`, so the inner sum has absolute value `O(P)`. Write uniquely
\[
 b=d u^2,\qquad b'=d v^2,\qquad d\ {\rm squarefree}.
\]
The number of such pairs with `b,b' <= 2B` is at most
\[
 \sum_{\substack{d\le2B\\d\ {\rm squarefree}}}
 \left\lfloor\sqrt{2B/d}\right\rfloor^2
 \le 2B\sum_{d\le2B}{1\over d}\ll B\log(2B).
\]
Taking absolute values of the coefficients in (3.2) proves (3.1). This proof is uniform over all bounded complex `beta_b`; no smoothness of `beta` is required. In particular, extending primes to composite Jacobi denominators introduces no unaccounted principal nonsquare case. ∎

### 3.2 Mellin separation and the final exponent

Modulo an odd prime, the only real characters are the principal character and the quadratic character. The latter is odd exactly when `p == 3 (mod 4)`. Hence there is at most one real odd character per `p`.

Define
\[
 \widetilde U(t)=\int_0^\infty U(x)x^{-it}{dx\over x},\qquad
 U(x)={1\over2\pi}\int_{\mathbb R}\widetilde U(t)x^{it}\,dt.
\]
The transform is rapidly decreasing, so its absolute integral is finite. Using `BQ=AP`, separate
\[
 U\left({bq\over pA}\right)
 ={1\over2\pi}\int\widetilde U(t)
       (b/B)^{it}(q/Q)^{it}(p/P)^{-it}\,dt.               \tag{3.3}
\]
For every real `t`, the `b` coefficients have modulus at most `||V||_infinity`, and the prime `q` sum satisfies
\[
 \left|\sum_{q\sim Q} Z(q/Q)(q/Q)^{it}\log q\left({q\over p}\right)\right|
 \ll Q.                                                  \tag{3.4}
\]
This is a trivial absolute-value bound using Chebyshev; no cancellation in `q` is presumed.

Cauchy–Schwarz over primes, (3.1), and `# {p ~ P} << P/log P` give for the real odd part of (2.6)
\[
 \begin{aligned}
 |D_{0,\mathrm{real\ odd}}|
 &\ll {Q\log P\over P}
       \left({P\over\log P}\right)^{1/2}
       \left(PB\log(2B)+B^4\right)^{1/2}\\
 &\ll Q\sqrt{B\log P\log(2B)}
       +QB^2\sqrt{{\log P\over P}}\\
 &\ll X^{19/20}\log X+X^{4/5}(\log X)^{1/2}
 \ll X^{19/20}\log X.
 \end{aligned}                                          \tag{3.5}
\]
All bounds used under the Mellin integral are uniform in `t`.

This also proves the assertion for the real odd portion of the **exact** character expansion (2.7). Indeed,
\[
 U(t+\epsilon_p)+U(t-\epsilon_p)-2U(t)=O(\epsilon_p^2).
\]
Since there is at most one such character per `p`, its total coefficient-replacement error is
\[
 \ll {BQ\over A^2}\sum_{p\sim P}{\log p\over p^2(p-1)}
 \ll {BQ\over A^2P^2}=X^{-1}.                            \tag{3.6}
\]
This last observation does not use Brun–Titchmarsh.

## 4. Audit of the inverse-residue Fourier identity

Set `r=p/P`, `s=q/Q`, and
\[
 \mathcal W_{r,s}(y)=V(y)U(sy/r).
\]
This is the function called `W_{r,s}` in the question; the calligraphic letter distinguishes it from the original prime weight `W`.
Let `x= inverse(q) (mod p)`, represented in `{1,...,p-1}`. Poisson summation in a residue class gives
\[
 \sum_{b\equiv a\ (p)}\mathcal W_{r,s}(b/B)
 ={B\over p}\sum_{h\in\mathbb Z}
       \widehat{\mathcal W}_{r,s}(hB/p)e(ha/p).
\]
The `b` sum in (2.2) is consequently
\[
 {B\over p}\sum_{h\in\mathbb Z}\widehat{\mathcal W}_{r,s}(hB/p)
       [e(-hx/p)-e(hx/p)].                              \tag{4.1}
\]
The zero frequency is zero. Since the weights are real,
`widehat(mathcal W)(-xi) = conjugate(widehat(mathcal W)(xi))`.
Pairing `h` and `-h`, with `h>0`, gives
\[
 (-2i)\sin(2\pi hx/p)
 \left[\widehat{\mathcal W}_{r,s}(hB/p)
       -\widehat{\mathcal W}_{r,s}(-hB/p)\right]
 =4\,\Im\widehat{\mathcal W}_{r,s}(hB/p)\sin(2\pi hx/p).
\]
Both the sign and the factor four are thus fixed by the stated Fourier convention.
As `B/p=1/(Hr)`, define
\[
 k(r,s,z)={4W(r)Z(s)\over r}
              \Im\widehat{\mathcal W}_{r,s}(z/r).         \tag{4.2}
\]
Equations (2.4) and (4.1) prove
\[
 \boxed{
 D={1\over H}\sum_{h\ge1}\sum_{p,q\ {\rm prime}}
 \log p\log q\,
 k\left({p\over P},{q\over Q},{h\over H}\right)
 \sin\left({2\pi h\,\overline q\over p}\right)+O(1).
 }                                                       \tag{4.3}
\]
The infinite series is absolutely convergent for each fixed `X`. The only approximation in (4.3) is the proved centering error. In particular, the zero mode vanishes for `D_0`; possible uncentered shift effects, including a zero-mode effect, have not silently been discarded.

### 4.1 Uniform kernel bounds

The kernel is compactly supported in `(r,s)` inside `(1,2)^2`. The `y` support is in the fixed support of `V`; all `r,s,y` derivatives of `V(y)U(sy/r)` are uniformly bounded on the relevant compact sets.

For real weights,
\[
 \Im\widehat{\mathcal W}_{r,s}(z/r)
 =-\int \mathcal W_{r,s}(y)\sin(2\pi zy/r)\,dy.
\]
Thus `k` is smooth and odd as a function of real `z`, and
\[
 k(r,s,z)= -{8\pi W(r)Z(s)\over r^2}\,
       z\int y V(y)U(sy/r)\,dy+O(z^3)                   \tag{4.4}
\]
uniformly after any fixed number of `r,s` derivatives. The explicit minus sign in the first-order formula (4.4) is consistent with the positive factor four in (4.2); the actual coefficient's sign depends on the real weights.

Repeated integration by parts in `y`, with additional integrations to absorb factors of `z` produced by parameter differentiation, gives the useful joint estimate
\[
 \left|\partial_r^a\partial_s^b(z\partial_z)^c k(r,s,z)\right|
 \le C_{a,b,c,N}\,z(1+z)^{-N}\qquad(z>0).              \tag{4.5}
\]
Consequently `k=O(z)` at zero and is Schwartz at infinity, uniformly in the required parameters. It would be incorrect to assert that **every ordinary `z` derivative** is `O(z)` at zero; the first derivative is usually nonzero. The correct fact needed below is that
\[
 \ell(r,s,z)=k(r,s,z)/z
\]
extends smoothly to `z=0` and has uniformly bounded `r,s` derivatives for `0 <= z <= 1`.

## 5. Ordinary large sieves: exact odd projection and normalizations

For prime `p ~ P` and coefficients `alpha_p`, let `beta_n` be a common coefficient sequence supported in an interval of length `O(Q)`, such as `Q<n<2Q`. Terms with `p|n` are omitted from expressions using an inverse. Define
\[
 S_h=\sum_{p\sim P}\alpha_p
       \sum_{\substack{n\sim Q\\(n,p)=1}}
             \beta_n\sin(2\pi h\overline n/p).
\]
We prove, for `R >= 1`,
\[
 \boxed{
 \sum_{1\le h\le R}|S_h|^2
 \ll (R+P^2){P^2+Q\over P}\,
       \|\alpha\|_\infty^2\sum_n|\beta_n|^2.
 }                                                       \tag{5.1}
\]
The prime restriction on `n` is unnecessary for (5.1). The prime restriction on the moduli `p` is important.

### 5.1 Additive large sieve, with a proof up to an absolute constant

For points `theta_j` separated by at least `Delta` on `R/Z`, and an interval `I` of `N` consecutive integers,
\[
 \sum_{h\in I}\left|\sum_j c_j e(h\theta_j)\right|^2
 \ll (N+\Delta^{-1})\sum_j|c_j|^2.                      \tag{5.2}
\]
To see this without a logarithmic loss, take `T=max(N,Delta^(-1))` and let `c` be the center of `I`. The nonnegative majorizing weight
\[
 w(t)=\left({\sin(\pi(t-c)/(2T))\over\pi(t-c)/(2T)}\right)^2
\]
is bounded below by an absolute positive constant on `I`. Its Fourier transform is
\[
 \widehat w(\xi)=2T e(-c\xi)(1-2T|\xi|)_+,
\]
supported in `[-1/(2T),1/(2T)]`. Poisson summation shows
\[
 \sum_{h\in\mathbb Z}w(h)e(h(\theta_j-\theta_k))
 =\begin{cases}2T,&j=k,\\0,&j\ne k.\end{cases}
\]
Indeed, every nonzero circular separation is at least `Delta`, greater than the Fourier support radius. The summations with `w` are absolutely convergent; Poisson for this squared-sinc kernel follows directly from its triangular Fourier transform (or by a limiting regularization). Expanding the weighted square proves (5.2). By finite-dimensional Hilbert-space duality, the transposed form also holds:
\[
 \sum_j\left|\sum_{h\in I}b_h e(h\theta_j)\right|^2
 \ll(N+\Delta^{-1})\sum_{h\in I}|b_h|^2.                \tag{5.3}
\]
Distinct reduced fractions `a/p`, with `p ~ P` prime and `1 <= a < p`, are separated on the circle by at least `1/(4P^2)`. Hence both versions have the usual factor `N+P^2`.

### 5.2 Character large sieve for the odd characters

Put
\[
 B_p(\chi)=\sum_n\beta_n\chi(n),\qquad
 T(\theta)=\sum_n\beta_n e(n\theta).
\]
An odd character modulo a prime is nonprincipal and primitive. Its Gauss sum satisfies
\[
 |\tau(\overline\chi)|^2=p,\qquad
 B_p(\chi)={1\over\tau(\overline\chi)}
           \sum_{a=1}^{p-1}\overline\chi(a)T(a/p).       \tag{5.4}
\]
For completeness, the finite Fourier identity in (5.4) follows by replacing `a` with `n^(-1)a` for `p` not dividing `n`; both sides are zero when `p|n`. The norm identity follows by expanding the square and putting `a=tb`: the sum over `b != 0` is `p-1` for `t=1` and `-1` otherwise, and a nonprincipal character has zero sum.

Extending a nonnegative sum of squares from odd characters to all characters and applying orthogonality gives
\[
 {1\over p-1}\sum_{\chi(-1)=-1}|B_p(\chi)|^2
 \le {1\over p}\sum_{a=1}^{p-1}|T(a/p)|^2.
\]
Sum over `p`, use `1/p <= 1/P`, and apply (5.3):
\[
 \sum_{p\sim P}{1\over p-1}
       \sum_{\chi(-1)=-1}|B_p(\chi)|^2
 \ll {P^2+Q\over P}\sum_n|\beta_n|^2.                  \tag{5.5}
\]
This is exactly the required character large sieve; no extra logarithm has entered.

### 5.3 Odd residue projection, followed by the other additive large sieve

Let
\[
 T_p(a)=\sum_{n\equiv a\ (p)}\beta_n\quad(a\ne0).
\]
For `x != 0`, set
\[
 c_{p,x}={\alpha_p\over2i}
        \left[T_p(x^{-1})-T_p(-x^{-1})\right].
\]
Then, including the sine normalization,
\[
 S_h=\sum_{p\sim P}\sum_{x=1}^{p-1}c_{p,x}e(hx/p).     \tag{5.6}
\]
Multiplicative Parseval gives
\[
 \sum_{a=1}^{p-1}|T_p(a)-T_p(-a)|^2
 ={4\over p-1}\sum_{\chi(-1)=-1}|B_p(\chi)|^2,
\]
so
\[
 \sum_{p,x}|c_{p,x}|^2
 =\sum_p{|\alpha_p|^2\over p-1}
                    \sum_{\chi(-1)=-1}|B_p(\chi)|^2.    \tag{5.7}
\]
Apply (5.2) to (5.6), followed by (5.5), to obtain (5.1).

The odd projection is essential here: it removes the principal characters before the Gauss-sum/primitive-character step. Including them as if they had Gauss norm `sqrt(p)` would be erroneous. Also, arbitrary composite or prime-power moduli cannot simply be substituted for the prime `p` in this proof.

## 6. Prime weights and uniform Mellin separation of the kernel

For the actual weights on primes, including arbitrary Mellin phases of modulus one,
\[
 \|\alpha\|_\infty^2\ll(\log P)^2,\qquad
 \sum_q|\beta_q|^2\ll Q\log Q.
\]
Since `R <= H < P^2` and `Q < P^2`, (5.1) gives
\[
 \sum_{h\le R}|S_h|^2\ll P^3Q(\log X)^3.              \tag{6.1}
\]
Here “Lambda weights” means precisely `log p` and `log q` on primes, as in the question, not an unnoticed change to all prime powers.

Define the low-frequency part of the **centered Fourier expression** by
\[
 D_{\le R}={1\over H}\sum_{1\le h\le R}\sum_{p,q}
 \log p\log q\,k(p/P,q/Q,h/H)
                \sin(2\pi h\overline q/p).
\]
This definition does not allocate the separate `O(1)` centering error to a frequency range.
For `0 <= z <= 1`, take the two-variable Mellin transform of `ell=k/z`:
\[
 L(t,u;z)=\int_0^\infty\int_0^\infty
             \ell(r,s,z)r^{-it}s^{-iu}{dr\over r}{ds\over s}.
\]
Compact support and the uniform `r,s` derivative bounds proved in Section 4 imply, for every `N`,
\[
 |L(t,u;z)|\le C_N(1+|t|)^{-N}(1+|u|)^{-N}
 \quad(0\le z\le1).                                    \tag{6.2}
\]
Mellin inversion now writes
\[
 D_{\le R}={1\over(2\pi)^2H^2}\int_{\mathbb R^2}
       \sum_{h\le R}h L(t,u;h/H)S_h(t,u)\,dt\,du,       \tag{6.3}
\]
where in `S_h(t,u)` the coefficients are
`alpha_p=(log p)(p/P)^(it)` and `beta_q=(log q)(q/Q)^(iu)`, restricted to the respective prime intervals. The original `W,Z` and the coupling to `U,V` are in `L`.

The transform in (6.3) is allowed to depend on `h`. No unsupported separation of this dependence is needed: Cauchy–Schwarz in `h` gives
\[
 \left|\sum_{h\le R}hL(t,u;h/H)S_h(t,u)\right|
 \le\left(\sum_{h\le R}h^2|L(t,u;h/H)|^2\right)^{1/2}
      \left(\sum_{h\le R}|S_h(t,u)|^2\right)^{1/2}.
\]
Use (6.1), (6.2), `sum_{h<=R} h^2 << R^3`, and integrate. This proves
\[
 \boxed{
 |D_{\le R}|\ll {P^{3/2}Q^{1/2}R^{3/2}\over H^2}
                    (\log X)^{3/2}
 =X^{7/20}R^{3/2}(\log X)^{3/2}.
 }                                                       \tag{6.4}
\]
Thus `h <= X^(2/5)` contributes at most `X^(19/20) (log X)^(3/2)`.

## 7. Audit of the circle-method statements

Define
\[
 F(\alpha)=\sum_{a,p}U(a/A)W(p/P)\log p\,e(\alpha ap),\qquad
 G(\alpha)=\sum_{b,q}V(b/B)Z(q/Q)\log q\,e(\alpha bq).
\]
Reality of the weights ensures that the coefficients of `F conjugate(G)` are the original real weights. Fourier orthogonality on the circle gives
\[
 \boxed{
 D=-2i\int_{-1/2}^{1/2}\sin(2\pi\alpha)
                  F(\alpha)\overline{G(\alpha)}\,d\alpha.
 }                                                       \tag{7.1}
\]
Indeed, the multiplier is `e(-alpha)-e(alpha)`, selecting coefficient `+1` minus coefficient `-1`. The integral is real after multiplication by `-2i`, as is also clear from conjugate symmetry.

### 7.1 Noncentral small-denominator arcs

Fix `delta>0`. On the circle, consider reduced noncentral fractions `c/r`, with representatives `1 <= c < r`, and
\[
 2\le r\le AX^{-\delta},\qquad
 \alpha=c/r+\theta\pmod1,\qquad
 |\theta|\le {1\over8rP}.                              \tag{7.2}
\]
For large `X`, every such `r` is less than every contributing `p`. Since `p` is prime, `(p,r)=1`, and hence `cp` is a nonzero residue modulo `r`. Therefore
\[
 \|\alpha p\|\ge\|cp/r\|-|\theta|p
 \ge {1\over r}-{1\over4r}={3\over4r}.                 \tag{7.3}
\]
This is the exact place where primality and `r<p` are used.

Smooth Poisson summation in `a` yields
\[
 \sum_a U(a/A)e(\alpha pa)
 =A\sum_{m\in\mathbb Z}\widehat U(A(m-\alpha p)).        \tag{7.4}
\]
For any prescribed nonnegative integer `J`, Schwartz decay (using a larger decay order if necessary) implies
\[
 \left|\sum_a U(a/A)e(\alpha pa)\right|
 \ll_J A(1+A\|\alpha p\|)^{-J}
 \ll_J A(r/A)^J.
\]
The bound on the entire `m` sum follows by isolating the nearest integer and bounding the other terms by a convergent tail; it is not just a bound on a single Poisson term.
Chebyshev then gives, uniformly on these arcs,
\[
 F(\alpha)\ll_J X(r/A)^J\ll_J X^{1-J\delta}.           \tag{7.5}
\]
For every fixed `M`, taking `J` sufficiently large in terms of `M,delta` makes this `O_{M,delta}(X^{-M})`.
Also `|G(alpha)| << BQ=X`, so the contribution of the **union** of these arcs to (7.1) is at most
\[
 O_J(X^{2-J\delta}),                                   \tag{7.6}
\]
and is likewise rapidly decreasing. Bounding a union of arcs requires no factor for the number of arcs; its measure is at most one. They are in fact disjoint for sufficiently large `X`, but disjointness is not needed for (7.6).

This conclusion is only about the arcs (7.2), not all noncentral rationals or all other parts of the circle. Without the noninteger-center convention, (7.3) is false: `c=r=1`, `alpha=1` gives `||alpha p||=0`.

### 7.2 Central arc

Use the centered representative and assume
\[
 |\alpha|\le {1\over8P}.
\]
Then `|alpha p| <= 1/4`. In (7.4), the term `m=0` is bounded by
\[
 C_J A(1+X|\alpha|)^{-J},
\]
since `Ap >= AP=X`. For `m != 0`, one has `|m-alpha p| >= (3/4)|m|`, giving a total `O_J(A^{1-J})` per prime, for `J>1`. Summing the prime weights proves
\[
 F(\alpha)\ll_J X(1+X|\alpha|)^{-J}+XA^{-J}.            \tag{7.7}
\]
There are no omitted nonzero Poisson modes in this bound.

Using `|G| << X` and `|sin(2 pi alpha)| << |alpha|`, the central contribution to (7.1), in absolute value, is at most
\[
 C_J X^2\int_{|\alpha|\le1/(8P)}
             |\alpha|(1+X|\alpha|)^{-J}\,d\alpha
 + C_J X^2 A^{-J}\int_{|\alpha|\le1/(8P)}|\alpha|\,d\alpha.
\]
For `J>2`, the first term is `O(1)` by the substitution `t=X|alpha|`; the second is
\[
 O_J(X^2P^{-2}A^{-J})=O_J(A^{2-J})=O(1).                \tag{7.8}
\]
Thus the stated `O(1)` central contribution, including its nonzero-mode error, is correct.

## 8. Limitations and exact exponent ledger

The verified powers are:

| Quantity | Power of `X` (logs omitted) |
| --- | ---: |
| `PB` in the quadratic moment | `7/10` |
| `B^4` in the quadratic moment | `2/5` |
| `Q sqrt(B)` in the real-odd bound | `19/20` |
| `Q B^2 / sqrt(P)` in its error term | `4/5` |
| `P^3 Q` in the short-`h` second moment | `27/10` |
| `P^(3/2) Q^(1/2) / H^2` | `7/20` |
| Low-frequency bound with `R=X^(2/5)` | `19/20` |
| The same bound with `R=H` | `11/10` |
| Centering error `BQ/(AP)` | `0` |

In particular:

* The quadratic calculation only handles the real odd characters, not the complex odd characters.
* Formula (6.4) at `R=H` is only `O(X^(11/10) (log X)^(3/2))`. The range `X^(2/5)<h` with `h` comparable to `H` is not negligible by this argument. Kernel decay only disposes of frequencies sufficiently far above `H`; it does not remove frequencies comparable to `H`. This describes the limitation of that large-sieve estimate, not the best bound on the entire original count: (2.3) already gives the trivial `|D| << BQ sum_p (log p)/p << X`.
* For example, for fixed positive `epsilon`, the tail `h>H X^epsilon` is arbitrarily power-small after taking sufficiently many kernel derivatives/integrations by parts: the trivial estimate is `O_N(PQ (X^epsilon)^(1-N))`. This is not a bound on the intervening frequencies.
* The circle argument leaves the complement of the stated central and small-denominator arcs untreated. No assertion about that complement follows by calling all the other arcs “noncentral.”
* The character, inverse-residue, and circle descriptions are different decompositions of the same count. Their saved pieces do not exhaust the count merely by being listed together.
* All logarithms in the claimed bounds are accounted for: in (3.5) one uses the prime count `P/log P`, and in (6.1) one uses `sum_q (log q)^2 << Q log Q`. Replacing these by integer counts would change the logarithmic powers.

**Exact audit conclusion:** (i), (ii), and (iii) supply the advertised auxiliary savings after explicitly centering the weight, restoring the coefficient norm, preserving the prime-modulus restriction, and specifying noncentral circle representatives. Their signs and the exponents `0.95`, `0.35`, and the logarithmic powers are correct. The literal centered coefficient is not the exact coefficient of the original `D`, and the unqualified `c != 0` condition is not sufficient on its own. No proof of the target or of a full power-saving bound for `D` is obtained.

## 9. Finite verification

Run from the repository root:

```sh
python3 -B Submission/DirectOddCountVerification.py
```

The script uses no third-party packages and reads no project files. It checks:

1. Its exact cyclotomic arithmetic against known cyclotomic polynomials and `product_{d|n} Phi_d = x^n-1`.
2. The negative centered odd-character coefficient, the exact shifted even/odd coefficient, and the classification/parity of real characters for small prime moduli.
3. Odd-residue Parseval with its factor `4/(p-1)`, and the inverse-residue sine coefficient identity.
4. Prime Gauss norms and their finite Fourier identities.
5. The exact finite-periodic Fourier counterpart of the positive-four pairing and its `1/p` normalization.
6. Jacobi multiplicativity, the `8n` period and zero complete mean for tested positive nonsquares, and the square-pair parametrization.
7. The circle multiplier sign and exact elimination of `a`; a rational finite fixture also verifies that centering is genuinely a change of the count, not an identity.
8. Exact finite rational checks of the arc constants and the integer-center exception.
9. All scale and exponent identities listed above.

The initial verification completed with all nine groups and **30,141 exact assertions passing**. After adding the primitive-completion and general-exponent checks for sections 10--11, the current run passes **all ten groups and 262,579 exact assertions**. Its output is in `DirectOddCountVerification.log`.

These checks do not prove uniform analytic estimates, Poisson summation for all smooth functions, Brun–Titchmarsh, or the target problem. Those analytic claims rest on the proofs and explicitly stated classical input in this note. The script output is recorded separately in `DirectOddCountVerification.log` after execution.

## 10. Stronger quadratic completion and a whole high-factor region

The elementary complete-period estimate in section 3 can be strengthened.
This disposes of real odd characters throughout the above-square-root
region, but still does not estimate the nonreal characters.

### 10.1 A uniform Jacobi interval bound

For a positive nonsquare N write N=d s^2, with d>1 squarefree, and put
D=d if d=1 mod 4, and D=4d otherwise. The fundamental-discriminant
character kappa_D is nonprincipal and primitive of conductor D<=4d.
Extend (N/r) by zero for even r. Then on all positive integers r,

```
J_N(r) = kappa_D(r) 1_{gcd(r,2s)=1}.
```

In particular, this includes the zeros arising from the square part of N;
they must not be dropped. Mobius inversion of the indicator, followed by
complete multiplicativity, writes any interval sum of J_N as at most
2^omega(2s)<=2s interval sums of kappa_D, multiplied by coefficients of
absolute value at most one. Terms with gcd(e,D)>1 are zero. The ordinary
primitive Polya--Vinogradov bound gives, uniformly in the interval,

```
|sum_{r in I} J_N(r)| << 2s sqrt(D) log(2D)
                       << sqrt(N) log(2N).               (10.1)
```

For reference, the primitive bound follows directly from its finite Fourier
expansion, |tau(kappa_D)|=sqrt(D), and
sum_{j=1}^{D-1} |sum_{r in I} e(jr/D)| << D log(2D), after removing
complete periods. The standard theorem and Gauss normalization were also
source-checked in arXiv:1107.0381, lines 17--27 and 377--390. No zero-free
region, prime equidistribution, or unproved character hypothesis is used.

Replacing the nonsquare O(B^2) estimate in section 3 by (10.1) proves,
for every common coefficient sequence beta supported on B<b<2B,

```
sum_{p~P, p prime} |sum_b beta_b (b/p)|^2
 << ||beta||_infinity^2 (PB+B^3) log(2B).                 (10.2)
```

The proof is otherwise unchanged: extend the nonnegative sum to odd
moduli r~P, open the square, bound the O(B log B) square pairs by O(P),
and the O(B^2) nonsquare pairs by O(B log B). The coefficients must be
common across the moduli; Mellin separation below supplies precisely that.

### 10.2 General exponent rectangle

Let P=X^alpha,Q=X^beta,A=X/P,B=X/Q, with fixed

```
1/2 < alpha <= beta < 1.
```

Use the same four fixed smooth weights and the same Lambda-weighted signed
count as before. Define its real-odd character component using the exact
character expansion in section 2. There is only one real odd character
per prime modulus, occurring at p=3 mod 4. Mellin inversion of U(bq/(pA))
gives common b coefficients V(b/B)(b/B)^(-it), bounded uniformly in t.
The q polynomial, including log q, has absolute value O(Q) by Chebyshev.
Using (10.2), the prime count P/log P, and Cauchy in p gives

```
|D_real,odd| << Q sqrt(B log P log(2B))
             + Q B^(3/2) P^(-1/2) sqrt(log P log(2B))
             + O(X^(-1))
 << [X^((1+beta)/2) + X^((3-alpha-beta)/2)] log X.        (10.3)
```

Both exponents are strictly below one. This estimate is uniform on compact
exponent regions with beta<=1-delta and alpha+beta>=1+delta, apart from the
fixed smooth-weight constants. Consequently it remains o(X) after the
O(log^2 X) dyadic subdivisions of such a region.

There are two details in applying the exact expansion:

* A possible p=q contributes zero to every character polynomial and to the
  original congruence count, so it causes no diagonal exception here.
* The exact odd coefficient is -[U(t+epsilon_p)+U(t-epsilon_p)], whereas
  the centered one is -2U(t), with epsilon_p=1/(pA)=O(X^(-1)). Taylor's
  theorem bounds their difference by O(X^(-2)). There is only one real odd
  character per modulus, so its total error is O(BQ X^(-2))=O(X^(-1)).
  Thus no whole-count Brun--Titchmarsh centering argument is needed in this
  generalized real-character assertion when P and Q are comparable.

For the original alpha=3/5,beta=9/10 example, the second exponent in
(10.3) improves from 4/5 to 3/4, while the leading one remains 19/20.
The necessary nonreal odd-character sum is unchanged and unestimated.

## 11. An explicit remaining Type II functional

Return to the original .6/.9 scales and kernel k from section 4. Replacing
the q prime sum weighted by log q by full Lambda(q) in the *direct count*
costs O(B sqrt(Q) log^2 X)=O(X^(11/20) log^2 X): after fixing b and a
proper prime power q, each neighbor bq+/-1 has at most one prime divisor
p in (P,2P), since P^2 is larger than that neighbor. The cofactor a is
then determined. Centering this full-Lambda count still costs O(1): the
prime part has the earlier O(1) bound, and the proper-power part has the
same divisor-count bound with an additional Taylor factor X^(-1), hence
O(X^(-9/20) log^2 X).

One must check the low-frequency part separately before carrying this
replacement through a Fourier truncation. For R=X^(2/5), the proper-power
low-frequency error has the elementary bound

```
(1/H) sum_{h<=R} O(h/H) O(P sqrt(Q) log^2 X)
 << P sqrt(Q) R^2 H^(-2) log^2 X
 = X^(17/20) log^2 X.                                  (11.1)
```

Together with section 6, the full-Lambda low-frequency contribution is
therefore O(X^(19/20) log^(3/2) X), after absorbing (11.1). Frequencies
h>H X^epsilon are arbitrarily power-small for fixed epsilon>0 by the
uniform Schwartz bounds on k.

Apply the exact Vaughan identity in the q variable with z=X^(7/50).
Its Type I divisors are at most z^2=X^(7/25); the free variable therefore
has length at least X^(31/50), which exceeds the prime modulus p~X^(3/5)
by a fixed power. The periodic sine has complete mean zero under v->-v.
Smooth Poisson summation, with the actual k weight retained, eliminates
all these Type I terms to arbitrary power accuracy. Terms p|d vanish;
in the others the inversion permutation on units is preserved.

Write b_z(v)=sum_{c|v,c>z} Lambda(c). The remaining expression is exactly,
up to the stated sublinear error,

```
R_II = (1/H) sum_{X^(2/5)<h<=H X^epsilon} sum_{p prime} log p
         sum_{d>z,v>z, gcd(p,dv)=1}
           mu(d) b_z(v) k(p/P,dv/Q,h/H)
           sin(2 pi h inverse(dv mod p)/p),

D = R_II + O(X^(19/20) log^(3/2) X).                     (11.2)
```

The q support is part of k. The hard blocks include d,v~X^(9/20) and
h~H. No o(X) estimate for R_II is provided. In particular, listing the
real-character, low-frequency, and circle-arc savings does not eliminate
this term: those are different decompositions, not disjoint pieces of a
partition unless their intersections are separately controlled. Neither
(10.3) nor (11.2) is a proof of the original density theorem.

## 12. A critical smooth-frequency bound and removable exceptional pairs

This section retains the actual Type II coefficients from (11.2). It proves
an upper bound at the critical scale, **not a signed saving**. In particular,
an unrelated pointwise Mobius-trace saving cannot be multiplied into this
bound: the two arguments take absolute values in different orders.

Restrict to a balanced block d,v of size X^(9/20), and let E be any subset
of the pairs, independent of p and h. Insert a fixed smooth frequency
cutoff chi(h/T), supported on a compact subinterval of (0,infinity), in
the Type II functional. Denote the result by R_{E,T}. For T>=1,

```
|R_{E,T}| <<_N (P T/H^2)(1+T/H)^(-N) |E| log^2 X.       (12.1)
```

The constant depends on the fixed smooth weights, N, and their required
seminorms. Here P=X^(3/5), H=X^(1/2), and dv is of size Q=X^(9/10).
For the whole balanced block, |E|=O(Q), so for 1<=T<=H this says

```
|R_{E,T}| << X^(1/2) T log^2 X.                         (12.2)
```

At T=H this is X log^2 X, not o(X).

### 12.1 Poisson and the full inverse-residue tail

Put alpha=T/H. Extend chi(u) k(r,s,alpha u) oddly to the real line, calling
the resulting smooth function F_alpha. Since the support avoids zero,
there is no regularity issue at zero. The k bounds in section 4 imply,
for every prescribed derivative/Schwartz seminorm and every N,

```
seminorm(F_alpha) <<_N alpha (1+alpha)^(-N).
```

Poisson, with the Fourier convention of section 1, gives the exact identity

```
(1/H) sum_{h>=1} chi(h/T) k(r,s,h/H) sin(2 pi h theta)
 = T/(2iH) sum_{j in Z} Fhat_alpha(T(j-theta)).           (12.3)
```

Therefore its absolute value is at most

```
C_(J,N) (T/H)^2 (1+T/H)^(-N)
  sum_{j in Z} (1+T|theta-j|)^(-J).                     (12.4)
```

For q=dv coprime to p, choose 1<=x<=p-1 with xq=1 mod p and take
`theta=x/p`. The integers b=x-jp, j in Z, are exactly all integers with
bq=1 mod p; they are nonzero. Both signs of b must be retained. Since
p is in (P,2P), the weight in (12.4) is bounded by a constant times
(1+|b|/M)^(-J), where M=P/T. For each fixed q,b,

```
sum_{p in (P,2P), p prime, p | bq-1} log p <= log|bq-1|. (12.5)
```

The integer bq-1 is nonzero since q>=2; if its absolute value is 1, both
sides are zero. It is essential to sum the entire tail: it is NOT valid
to replace log|bq-1| pointwise by O(log X) for unbounded b.
For J>=3 and M>=1, a dyadic decomposition gives

```
sum_{b != 0} (1+|b|/M)^(-J) log|bq-1|
 <<_J M log(2q(1+M)).                                   (12.6)
```

If 0<M<1, bounding the weight by (M/|b|)^J instead gives
O_J(M^J log(2q)), and this is also O_J(M log(2q)). Since T>=1, we have
M<=P; consequently either case is O_J((P/T) log X).
Combine (12.4)--(12.6), |mu(d)|<=1, and
0<=b_z(v)<=log v=O(log X) to obtain (12.1). No primality of q, no
coprimality of d and v, and no independence of their coefficients have
been used.

### 12.2 Smooth partition and lower frequencies

A genuine finite-overlap smooth partition on (0,infinity) into scales
T=2^j, j>=0 (with a separate initial piece if needed), lets us sum
(12.1). The dyadic sum of T(1+T/H)^(-N) is O_N(H) for N>1; hence

```
all smoothly partitioned frequencies:  << (P/H)|E| log^2 X.
```

The restricted sum over T<=H/log^A X is geometric, not logarithmic. On
the full block its bound is O(X log^(2-A) X), with no extra factor log X.
The cutoffs in a dyadic partition must overlap: translates of a smooth
function supported strictly inside [1,2] do not by themselves partition
unity. These conclusions concern smooth frequency pieces; they do not
automatically bound sharp truncations or separately character-projected
terms in another decomposition.

### 12.3 Gcd and squarefull exceptional sets

For d,v in fixed comparable intervals of length D=V=X^(9/20),

```
#{(d,v): gcd(d,v)>G} << DV/G,
#{(d,v): s(v)>S}     << DV/sqrt(S),                      (12.7)
```

where s(v) is the full squarefull part: the product of p^e over prime
powers p^e exactly dividing v with e>=2. The first estimate follows by
summing floor(CD/g) floor(CV/g) over g>G. For the second, every squarefull
integer is uniquely a^2 b^3 with b squarefree; hence the number of such
integers <=Y is O(sqrt(Y)). Dyadic summation gives
sum_{s>S, s squarefull} 1/s=O(S^(-1/2)). Count multiples of each such s
in v's interval, bounded by CV/s, and then sum over d.

These exceptional sets are independent of p,h. By (12.1) and the smooth
partition just described, they cost respectively

```
O(X G^(-1) log^2 X),   O(X S^(-1/2) log^2 X).            (12.8)
```

Taking G=X^eta and S=X^(2eta) makes both errors power-saving.

### 12.4 Exact factorization on the complement

Only squarefree d contribute, because mu(d)=0 otherwise. Write v=s t,
where s=s(v), t is squarefree, and gcd(s,t)=1. Let

```
g_s=gcd(d,s), g_t=gcd(d,t),
d_0=d/(g_s g_t), v_0=t/g_t, delta=s g_s g_t^2.
```

Then

```
dv=d_0 v_0 delta,
gcd(d_0,v_0)=gcd(d_0,delta)=gcd(v_0,delta)=1,
d_0 and v_0 are squarefree.
```

Indeed g_s,g_t are disjoint squarefree divisors of d, with product
gcd(d,v). Checking one prime valuation at a time also identifies delta
as the full squarefull part of dv. In particular, on the complement of
(12.7),

```
delta <= S G^2,
d_0 >> X^(9/20)/G,    v_0 >> X^(9/20)/(S G).             (12.9)
```

For G=X^eta,S=X^(2eta), these become delta<=X^(4eta),
d_0>>X^(9/20-eta), v_0>>X^(9/20-3eta).

This is an arithmetic factorization, not an independent-coefficient
bilinear decomposition. Reindexing must keep all multiplicities and the
exact coefficients

```
mu(d)=mu(d_0)mu(g_s)mu(g_t),
b_z(v)=b_z(s g_t v_0).
```

No signed logarithmic saving in the surviving main block has been
proved in this section, and none of these pilot estimates covers the
whole density problem.

## 13. What the critical bound does and does not combine with

This section records two independently checked continuations of section 12.
Neither obtains a signed saving for the remaining prime-weighted block.
Write L=log X, D=V=X^(9/20), B=P/H=X^(1/10). Insert nonnegative smooth
balanced cutoffs, and write alpha_d=mu(d)u(d/D), beta_v=b_z(v)w(v/V),
with |u|<=1 and 0<=w<=1. Thus beta_v>=0 and sum beta_v=O(VL).

### 13.1 Exact sparse norm at T=H

If chi is the even extension of the positive-frequency band cutoff, put
f_(r,s)(y)=chi(y)k(r,s,y), using the odd extension of k. This is real odd.
Define the real odd Schwartz function

```
W_*(r,s,t)=(1/(2i)) Fourier[f_(r,s)](-t/r).
```

Poisson as in (12.3) gives, with no remaining H factor,

```
R=sum_v beta_v sum_d alpha_d K(d,v),
K(d,v)=sum_{p~P prime} log p A_p(d,v),
A_p(d,v)=sum_{b>=1} W_*(p/P,dv/Q,b/B)
                       [1_(p|bdv-1)-1_(p|bdv+1)].       (13.1)
```

The sign follows by setting b=inverse(dv mod p)-jp in (12.3) and using
oddness of W_* for the negative b terms. The positive envelope of K,
obtained by replacing W_* by its absolute value and the bracket by the
sum of its two indicators, is O(BL), uniformly in d,v. This is the same
prime-divisor product and whole-tail argument as section 12.

Set F(v)=sum_d alpha_d K(d,v) and

```
M=sum_v beta_v |F(v)|^2.
```

Cauchy gives |R|^2<=O(VL)M. In this **single compatible norm**, the
baseline is M=O(V D^2 B^2 L^3)=O(X^(31/20)L^3). Hence a sufficient
relative bound is M=o(X^(31/20)/L).

The following pieces of its expansion are already small:

* The whole same-d contribution is O(V D B^2 L^3)=O(X^(11/10)L^3),
  directly from the positive envelope.
* The whole same-prime contribution is O(X L^4). To check this, truncate
  b<=B_*=P/(16D), with a power-small error by Schwartz decay since
  B_*/B is a positive power of X. With d<=2D, t=bd<=P/8. For the same p,
  t_1 v= sigma_1 mod p and t_2 v=sigma_2 mod p force sigma_1=sigma_2
  and t_1=t_2, since 0<t_i<P/8. For each t,v,sigma, at most one p~P
  divides tv-sigma, since tv+1<P^2 for sufficiently large X. The
  weighted product energy of b_1d_1=b_2d_2 is O(BD L): write
  b_1=g r,b_2=g s,(r,s)=1,d_1=s a,d_2=r a and sum over dyadic b ranges.
  Two prime logs, this energy, and sum beta_v=O(VL) give O(XL^4).
* The absolute contribution of pairs (d_1,d_2)>G is
  O(V D^2 B^2 L^3/G), using the positive envelope after expanding M.
  With G=L^6 it is O(X^(31/20)/L^3).

In the same-prime piece, equalities of t and dv do not require the
smooth factors for the two d's to be equal. Their absolute Schwartz
bounds, rather than equality of their values, give the energy bound.
The overlap with the same-d piece is nonnegative, so summing the two
upper bounds is legitimate for their union.

Let C_G be the remaining expansion with d_1!=d_2, (d_1,d_2)<=G,
p_1!=p_2, retaining alpha_(d_1)alpha_(d_2), beta_v, and both kernels.
A concrete SUFFICIENT EXTRA ESTIMATE is

```
|C_(L^6)| << X^(31/20)/L^2.                              (SC)
```

Together with the proved pieces it would give
R=O(X/sqrt(L)+X^(31/40)L^(5/2))=o(X). **(SC) is not proved.** It asks
for sparse-scale signed covariance, not for an inner pointwise Mobius
estimate. Its arithmetic factors are exactly

```
sum_{sigma_1,sigma_2=+/-1} sigma_1 sigma_2
  1_(p_1|b_1 d_1 v-sigma_1) 1_(p_2|b_2 d_2 v-sigma_2).
```

The complete v-period has zero mean by CRT for p_1!=p_2, but the actual
v-length X^(9/20) is below sqrt(p_1p_2)=X^(3/5). Complete cancellation
is not an estimate on that interval. Also mu(d_1)mu(d_2) cannot be
replaced by mu(d_1d_2) without coprimality. This second-moment criterion
is stronger than the original first-moment goal and is not asserted to
follow from it.

### 13.2 A short-divisor prime surrogate really does cancel

Let B(rho) denote the right side of (13.1), with the sum over primes p
and log p replaced by a sum over all positive m~P with coefficient
rho(m). Divisibility already enforces coprimality to dv. Fix eta>0 and
suppose

```
rho(m)=f_0(m/P) sum_{ell|m, ell<=Y_0} lambda_ell,
Y_0<=X^(1/20-eta), |lambda_ell|<=tau(ell)^C L^C,          (13.2)
```

with f_0 fixed smooth and the coefficients independent of the other
variables. Then the classical below-square-root Bombieri--Vinogradov
estimate for convolutions gives, for every A>0,

```
B(rho)=O_(A,eta,C)(X L^(-A)).                            (13.3)
```

Here the full balanced convolution is essential; this assertion is NOT
uniform over arbitrary subsets E of (d,v). An extra log m is allowed by
writing it as log P+log(m/P).

For the size and coefficient audit, first truncate b<=B X^(eta/2),
with an arbitrarily small power error from Schwartz decay and elementary
divisor bounds. In each sign switch bdv-sigma=a m. The exact condition
ell|m becomes a ell | bdv-sigma, and

```
a ~ bQ/P,   a ell << X^(9/20-eta/2)=Q^(1/2)X^(-eta/2).
```

Replacing (bdv-sigma)/(aP) in the smooth m-weight by bdv/(aP) makes the
weight common to the signs. Even after dropping the divisibility
condition, the mean-value bound and the harmonic a-sum bound its total
cost by O(Y_0 Q B/P L^O(1))=O(X^(9/20-eta)L^O(1)).

Retain the actual convolution

```
gamma(n)=sum_{dv=n} mu(d)u(d/D) b_z(v)w(v/V).
```

After removing a harmless log X coefficient bound, its factors are
divisor-bounded, and its Mobius factor is Siegel--Walfisz. Classical
convolution Bombieri--Vinogradov, including maximum reduced residue
classes and partial endpoints, applies with a fixed power margin at
the above moduli a ell. For (b,a ell)=1, the two residue classes are
+/-inverse(b), with identical coprime principal means. For noncoprime
b both are empty. Grouping a ell into its modulus costs a fixed
divisor-power weight; the standard weighted variant follows as well
by clipping that divisor weight and using divisor moments and arbitrary
logarithmic saving. Partial summation handles the common smooth weight,
uniformly in a,b. Finally the weighted b-sum is O(B), so the discrepancy
is O_A(BQ L^(-A))=O_A(X L^(-A)), as stated.

Source scope checked: Fouvry--Radziwill, arXiv:1811.08672,
`FouvryRadzi7.tex:45--58`, explicitly records the classical below-half
convolution theorem and cites BFI Theorem 0 / Opera de Cribro Theorem
9.16. The Siegel--Walfisz definition with the auxiliary coprimality
parameter and its validity for mu appear in Maynard, arXiv:2006.07088,
`WellFactorable.tex:179--186`. No beyond-half version is used here.

This does NOT approximate the prime weight with a negligible error.
For example, for Y=X^(1/40-eta) the nonnegative Selberg-type weight

```
rho_Y(m)=[sum_{ell|m,ell<=Y} mu(ell)(1-log ell/log Y)]^2
```

has an expansion of level <=Y^2 and equals 1 for primes m~P. Thus the
exact consequence is

```
R = -B((log m)rho_Y(m)1_(m composite)) + O_A(X L^(-A)).   (13.4)
```

The composite remainder includes proper prime powers and is not
estimated by (13.3). Subtracting upper sieve bounds or simply deleting
this remainder would be invalid. The available divisor level X^(1/20)
is far too short to characterize primes of size X^(3/5).

### 13.3 Two further non-cancellations

The exact symmetry d<->v leaves the kernel unchanged. For symmetric
cutoffs the coefficient becomes

```
[mu(d)b_z(v)+mu(v)b_z(d)]/2,
```

not zero. On the coprime squarefree sector this is
mu(d)[b_z(v)+mu(dv)b_z(d)]/2: the mu(dv)=+1 sector has a sum, not a
difference. Replacing b_z(v) by log v needs a separate argument.

Also, d with no divisor prime <=y<D include all primes d~D. Since
sum_{v~V}b_z(v)=V log(V/z)+O(V), that prime-d family has absolute
coefficient mass of order DV=Q. Its coefficient-sensitive sparse
envelope still costs O(XL), not o(X). This is an obstruction to that
absolute deletion argument, not a lower bound on its signed count.

No estimate in sections 12--13 proves the pilot's required signed
saving, and the original theorem has additional exponent regions.
