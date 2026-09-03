# Averaged shifts with the actual CRT/Maynard weights

## Outcome

**Erdős #5 is not proved. No factor below 2 is obtained.** This is an arithmetic attempt, not an assertion that all averaged approaches are impossible.

The main new repair is that **the covering residue need not vary with every selected tuple**. One can protect a growing pool in each of two narrow logarithmic bands, choose a *single* CRT residue first, and then select fixed-size tuples from those pools. Each pool has size comparable to `log N / log log N`; all but `O(1/log log N)` of the fixed-size selections have the source's smooth-difference property. Extra, unselected protected points do not spoil the two-band global-consecutivity argument.

For this repaired family I derive:

1. An exact expansion retaining the Maynard kernels. On a prime-pair summand the two endpoint divisor coordinates disappear, leaving a core weight independent of those endpoints.
2. An explicit averaged arithmetic-progression discrepancy identity and its proved `L2` bound, with the CRT inverse retained. The elementary evaluation of that bound is too large even at the density scale of a single large prime divisor.
3. An exact Ramanujan Gram formula. In the protected pools its off-diagonal correction is only `O(1/log log N)` relative to the diagonal; it does not supply a constant-factor saving in the completed/Cauchy argument.
4. A direct calculation showing why replacing the without-replacement tuple average by a product of empirical averages is invalid at main-term scale. This uses actual divisor kernels on the common CRT rows, not an unweighted prime model.

At the existing distribution level, averaging does not change the completed divisor main terms. The published Chen recipe has the same coefficient for every selected tuple, even with its distribution errors set to zero. A separate exact energy calculation gives the limitation of the simpler Selberg-square replacement. Neither calculation is an impossibility theorem for different signed arithmetic estimates or different detectors.

`Submission/Spec.lean` was not edited or used as a premise. No numerical search for prime gaps was performed.

## 1. Sources, weights, and normalization

Line references are to the following local TeX files, not to possibly different published numbering.

- **M18:** `/corpus/src/1811.03008/limitp2.tex`.
  - **174–189:** expected weighted pair main term, constants 4 and 3.99, and the significance of a factor below 2.
  - **208–225:** exceptional prime and modified Bombieri–Vinogradov, uniform in the reduced residue.
  - **353–390:** exact coefficient array, support, `B`, smooth differences, CRT hypothesis, and weighted pair upper bound.
  - **394–408:** removing the two endpoint divisor coordinates; the exceptional-prime indicator; Chen's three terms.
  - **461–519:** divisor expansion, AP main terms, and the already-negligible distribution error at the stated level.
  - **587–615, 638–677:** switched term, its distribution error, and the three main-term integrals.
  - **735–775:** occupancy statistic and symmetric integral estimates.
- **BFM:** `/corpus/src/1404.5094/banks-freiberg-maynard-limit-points-of-normalized-prime-gaps-arXiv.tex`.
  - **694–715, 770–784:** `Z_T` is 1 or a prime tending to infinity, and `Z_T/φ(Z_T)=1+o(1)`.
  - **1180–1266:** coefficients and the coprime divisor-sum evaluation.
  - **1280–1351:** `I_K,J_K,L_K` and mass/first/pair moments.
  - **1354–1414:** mass calculation, including its uniform `O(N^(2δ+o(1)))` counting error.
  - **1506–1625:** the one-prime-conditioned Selberg square and its derivative-energy coefficient.
- **Ford:** `/corpus/src/2101.03440/HR_shift.tex`, **87–90, 265–280**: the ordinary two-linear-form upper sieve with uniform constants. Below it is used only to count *small offset labels* having a bad difference, not to estimate primes under the CRT mask.
- **Lichtman:** `/corpus/src/2109.02851/lineartwin8.tex`, **84–94**: `π_2(x) ≤ (3.29956+o(1)) Π(x)`, where `Π(x)` already includes the factor 2 in the full Hardy–Littlewood main term. The multiplier is **not** 1.64978. This unweighted theorem is not inserted into a weighted sum here.

The checked preliminary covering input is in `InitialIntervalAmplificationAttempt.md`, §2, and `HeightControlledConstructionAttempt.md`, §2. The growing-pool extension below is proved explicitly.

Put

\[
 L=\log N,\qquad z=\eta L,\qquad Z=Z_{N^{4\eta}},\qquad
 W=\prod_{p\le z,\ p\ne Z}p,\qquad B=\frac{\phi(W)}W L.
 \tag{1}
\]

All geometric parameters, the tuple dimension `K`, the support parameter `δ`, and the smooth test functions are fixed before `N→∞`. Choose `η>0` sufficiently small for the published estimates. The exclusion of `Z` is vacuous when `Z=1` or `Z>z`.

The source coefficients, with its finite tensor rank denoted here by `R`, are

\[
 \lambda_{\mathbf d}
 =1_{(\prod_i d_i,Z)=1}\prod_i\mu(d_i)
       \sum_{r=1}^R\prod_{i=1}^K
                  F_{i,r}\left(\frac{\log d_i}{L}\right),
 \qquad \prod_i d_i\le N^\delta.
 \tag{2}
\]

For a labelled tuple `H=(h_1,…,h_K)`,

\[
 w_H(n)=\left(\sum_{d_i\mid n+h_i}\lambda_{\mathbf d}\right)^2,
 \qquad F(\mathbf t)=\sum_{r=1}^R\prod_iF'_{i,r}(t_i).
 \tag{3}
\]

The coefficient array in (2) can be the **same array** for all tuples. Its *evaluation* (3) is not the same function of `n`. The CRT restriction is also part of every sum.

For symmetric `F`, write `I=I_K(F)`, `J=J_K(F)`, `L_2=L_K(F)`. In particular,

\[
 L_2=\int_{\mathbb R_+^{K-2}}
       \left(\int_{\mathbb R_+^2}F(\mathbf t)\,dt_jdt_\ell\right)^2
       \prod_{i\ne j,\ell}dt_i.
\]

For an admissible tuple with all differences `z`-smooth and `gcd(∏(b+h_i),W)=1`, the source gives

\[
 \begin{split}
 \sum_{\substack{N<n\le2N\\n\equiv b\ (W)}}w_H(n)
     &=(1+o(1))\frac NW B^{-K}I,\\
 \sum_{\substack{N<n\le2N\\n\equiv b\ (W)}}1_{\mathbb P}(n+h_j)w_H(n)
     &=(1+o(1))\frac NW B^{-K}J,\\
 S_{H;j\ell}:=
 \sum_{\substack{N<n\le2N\\n\equiv b\ (W)}}
       1_{\mathbb P}(n+h_j)1_{\mathbb P}(n+h_\ell)w_H(n)
     &\le(3.99+O(\delta))\frac NW B^{-K}L_2.
 \end{split}                                                   \tag{4}
\]

The pair benchmark is `N W^(-1) B^(-K) L_2`, not half that quantity. It is a benchmark for one fixed distinct pair; unordered-pair combinatorics enters only when different pairs are summed.

Here is also a local normalization check. Conditional on the fixed CRT row, the unweighted two-prime benchmark is

\[
 \frac NW B^{-2}
 \prod_{p\nmid W}
  \frac{1-\nu_p(\{h_j,h_\ell\})/p}{(1-1/p)^2}.
\]

For `p>z`, smooth differences give `ν_p=2`. The corresponding product is `1+O(1/z)` by `Σ_{p>z}p^(-2)≪1/z`. The possible omitted prime contributes `1+O(1/Z)` when `Z>1`, even if it divides a difference. Thus this product is `1+o(1)`. There is no singular-series factor of 2 left to remove by averaging. This is a normalization calculation, **not** a prime-pair asymptotic.

## 2. Arithmetic repair: one CRT mask for a growing pool of tuples

### Proposition 1 — common protected pools

Fix `C>2` and two disjoint bands

\[
 1<\alpha_1<\beta_1<\alpha_2<\beta_2<C,
 \qquad \beta_g-\alpha_g<1.
 \tag{5}
\]

For sufficiently large `N` there are pools `T_g⊂(α_g z,β_g z)` and **one** residue `b mod W` such that:

- every point of `T_1∪T_2` survives the small-prime cover;
- every other integer in `[1,⌊Cz⌋]` is covered;
- for fixed positive constants `c_g`,

  \[
  M_g:=|T_g|=(c_g+o(1))\frac z{\log z};                 \tag{6}
  \]

- for any fixed `K_1,K_2`, a proportion `1-O(1/log z)` of ordered selections of `K_g` distinct members from `T_g` have **all** differences `z`-smooth. These selected tuples satisfy the source's admissibility and CRT conditions.

The constants and the threshold may depend on the bands and `K`; the exponent `η` need not depend on the diameter of the covering interval.

#### Proof: preliminary survivors

Choose a fixed sufficiently large `v≥max(3,2C,K)` and put

\[
 \sigma_v(m)=\prod_{\substack{p\le v\\p\nmid m}}\frac{p-2}{p-1},
 \qquad
 C\sum_{m\le\lfloor2C\rfloor}\frac{\sigma_v(m)}m<\frac1{16}.
 \tag{7}
\]

Such a fixed `v` exists. Initially choose the covering residue `a_p=1` for `p≤v` and `a_p=0` for `v<p≤z/2`, omitting `Z`. If `Z>1`, eventually `Z>v` by the cited exceptional-prime bound.

Let `S` be the survivors in `[1,⌊Cz⌋]`. A survivor either has only prime factors at most `v` and possibly `Z`, or is `mℓ` with `m≤2C` and `ℓ>z/2` prime. Two factors greater than `z/2` cannot occur for large `z`. In the latter case the cofactor is at most `2C≤v`, so cannot contain the omitted prime if it exceeds `v`.

The first class has size

\[
 O_v((1+\log z)^{\pi(v)+1})=o(z/\log z),
\]

uniformly in the omitted prime. PNT in the fixed progressions modulo `P(v)` bounds the second class by

\[
 \left(C\sum_{m\le2C}\frac{\sigma_v(m)}m+o(1)\right)
       \frac z{\log z}.
\]

Consequently

\[
 |S|\le\frac z{8\log z}                                  \tag{8}
\]

for large `z`. This is the same preliminary survivor estimate as in the checked protected cover; it does not yet use a number of protected points.

#### Proof: positively many eligible labels in each band

Take

\[
 T_g=\{2\ell\in(\alpha_gz,\beta_gz):
       \ell\text{ prime},\quad 2\ell\not\equiv1\pmod p
                                  \text{ for every }p\le v\}.
 \tag{9}
\]

These points are in `S`: their only prime factors are 2 and a prime `ℓ>z/2`. For `p=2` the small-prime condition is automatic; for odd `p≤v`, among the `p−1` reduced classes of `ℓ`, exactly `p−2` are allowed. Fixed-modulus PNT therefore gives

\[
 c_g=\frac{\beta_g-\alpha_g}{2}\sigma_v(2)>0
\]

in (6). These are primes of size comparable to **`z`**, used as offset labels. They are not the desired primes of size `N`. Some labels `2ℓ` have a prime factor above `z`; that is allowed. The source requires smooth **differences**, not smooth offsets. Protection of the whole pool is proved by the reserve construction next, rather than by applying the old fixed-smooth-point lemma outside its hypotheses.

#### Proof: the reserve works even though the protected set grows

Let `T=T_1∪T_2`. Reserve the primes in `(z/2,z]`, again omitting `Z`. There are `(1/2+o(1))z/log z` such primes.

For `t∈S\T` and `h∈T`, the nonzero integer `t−h` has absolute value at most `Cz`. For `z>4C` it has at most one prime divisor in the reserve. Thus, when covering `t`, at most `|T|` reserve primes are forbidden by protection. Fewer than `|S\T|` have already been used. By (8), their combined number is less than the reserve size. Assign a new eligible prime `p` and set `a_p=t mod p`.

Every unused reserve prime can be given a residue avoiding all of `T`, since `|T|≤|S|<z/2<p`. This completes the cover. Notice the useful cancellation in the capacity requirement:

\[
 \#\{\text{previously used primes}\}
 +\#\{\text{primes forbidden by protection}\}<|S|,
\]

not a bound involving a fixed protected dimension.

CRT supplies `b≡−a_p mod p` for all primes in `W`. Then every covered `n+t`, for `n∈(N,2N]`, is divisible by a prime at most `z` and is larger than that prime, hence is composite. All protected translates are coprime to `W`. The residue is chosen **before** a tuple is selected.

#### Proof: almost every fixed-size tuple has smooth differences

Within one band all differences have magnitude less than `z`, so are automatically `z`-smooth. For a cross-band pair `2ℓ,2ℓ'`, a bad difference has the form

\[
 |\ell-\ell'|=mp,\qquad p>z\text{ prime},
 \qquad 1\le m\le C/2.                                   \tag{10}
\]

For each fixed `m,p`, the ordinary two-linear-form sieve bounds the number of possible prime labels `ℓ',ℓ'+mp=O_C(z)` by

\[
 \ll_C\frac{mp}{\phi(mp)}\frac z{\log^2z}
 \ll_C\frac z{\log^2z}.
\]

There are `O_C(z/log z)` possible primes `p` and finitely many `m`. Thus the number of bad cross pairs is `O_C(z²/log³z)`, whereas `M_1M_2` is comparable to `z²/log²z`. A union bound over the fixed number `K_1K_2` of selected cross pairs proves the assertion.

For admissibility, eventually `Z>K` if `Z>1`. Every prime `p≤K` is then in `W`, and the residue `−b mod p` is missed by the selected shifts. A prime `p>K` cannot be covered by `K` shifts. This proves admissibility, including at the omitted prime. ∎

### What this repairs, and what it does not

The bands in (5) entail no restriction on a prescribed gap band `(a,b)`. Choose two positive original-coordinate bands of width less than `η`, with every cross difference strictly between `a` and `b`, and translate both bands to the right if necessary. Dividing their endpoints by `η` gives (5) for a sufficiently large fixed `C`.

On the common CRT rows, primes anywhere in the covered interval can occur only in `T_1∪T_2`. If both selected tuple groups contain a prime, take the **last actual prime in `T_1`** and the **first actual prime in `T_2`**. They are globally consecutive. They need not be selected tuple entries; unselected protected entries inside either band cause no problem. This distinction is essential.

Also,

\[
 W=N^{\eta+o(1)},\qquad
 B=(e^{-\gamma}+o(1))\frac L{\log z},\qquad
 \frac{M_g}{B}\longrightarrow
 \kappa_g=\frac{\eta e^\gamma\sigma_v(2)}2(\beta_g-\alpha_g)>0.
 \tag{11}
\]

The exceptional-prime omission changes these asymptotics by `1+o(1)`.

Let `G_N` be the good labelled tuples from Proposition 1. Their number is

\[
 |G_N|=(1-O(1/\log z))(M_1)_{K_1}(M_2)_{K_2},
\]

where `(M)_k` is a falling factorial. Thus a genuine average with a common mask exists. The source's pointwise occupancy statistic can legitimately be summed against `w_H(n)` over pairs `(n,H)` with `H∈G_N`; positivity would select an actual row and an actual good tuple. **The Maynard weight still varies with the selected shifts.** Moreover, the small fraction of bad tuples must not simply be discarded from an arbitrary weighted identity by cardinality alone. Below, source estimates are averaged directly over `G_N`, and identities for an unrestricted tuple average are explicitly identified as such.

## 3. Exact weight dependence after averaging

Define the one-coordinate divisor kernels

\[
 \xi_{i,r}(x)=\sum_{\substack{d\mid x\\(d,Z)=1}}
                    \mu(d)F_{i,r}(\log d/L).
\]

On the CRT rows, factors of `W` are automatically absent. Exactly,

\[
 w_H(n)=\sum_{r,s=1}^R\prod_{i=1}^K
                \xi_{i,r}(n+h_i)\xi_{i,s}(n+h_i).          \tag{12}
\]

Individual terms of this tensor expansion can have either sign, although `w_H≥0`.

On a prime-pair summand, `d_j=d_ℓ=1`, since their permitted divisors are below `N` and the endpoints exceed `N`. Therefore

\[
 1_{\mathbb P}(n+h_j)1_{\mathbb P}(n+h_\ell)w_H(n)
 =1_{\mathbb P}(n+h_j)1_{\mathbb P}(n+h_\ell)
       \left(\sum_{\substack{d_i\mid n+h_i\\d_j=d_\ell=1}}
                       \lambda_{\mathbf d}\right)^2.       \tag{13}
\]

For a fixed core `H\{h_j,h_ℓ}`, the last square is independent of the two endpoint positions. This is the useful endpoint averaging that the common CRT residue now makes legitimate.

M18 inserts the additional factor `1_{((n+h_j)(n+h_ℓ),Z)=1}` in its `ν_{H,jℓ}`. It equals 1 on the prime-pair summand, but must be retained when quoting the source's Chen estimates for composite endpoints. I do not drop it from those estimates. The elementary Selberg-majorant expansion in §4 uses the square in (13) without that indicator; that is a valid, potentially weaker, upper majorant, not a rederivation of the 3.99 estimate.

For example, put `a_i^{rs}(n,h)=ξ_{i,r}(n+h)ξ_{i,s}(n+h)`. The exact unrestricted tuple average of the weight is

\[
 \sum_{r,s}\prod_{g=1}^2
  \frac{1}{(M_g)_{K_g}}
  \sum_{\substack{(h_i)_{i\in G_g}\in T_g^{K_g}\\h_i\ \text{distinct}}}
                   \prod_{i\in G_g}a_i^{rs}(n,h_i).         \tag{14}
\]

For the good-tuple average, insert `1_{H∈G_N}` inside the combined sum and normalize by `|G_N|`; in general it no longer factors into the two sums in (14). Neither version is the product of the one-coordinate empirical means. Section 7 quantifies the failure of that replacement in a genuine source subclass.

## 4. The completed divisor main term is shift-independent

Here is a finite algebraic statement, before invoking any prime-distribution estimate.

Take a divisor-polynomial majorant

\[
 U(x)=\sum_{q\mid x}\rho_q\ge1_{\mathbb P}(x)
\]

for the range of `x` in question, with squarefree `q<N`, `(q,WZ)=1`. Use one coefficient array `ρ` for the tuple family. A Selberg square is one such choice. The coefficients may have either sign. Fix a good tuple and use (13), so that the core square is nonnegative and multiplication by this majorant is valid.

Expand the square. Put `r_i=[d_i,e_i]` for `i≠j,ℓ`. Any nonzero congruence count requires these `r_i` to be pairwise coprime and coprime to `WZ`. If `q` shares a prime with any `r_i`, its count is zero: that prime exceeds `z` but would divide the nonzero smooth difference `h_i−h_ℓ`. These are exact incompatibilities, not errors expected to cancel on average.

For a compatible term put

\[
 Q=W\prod_{i\ne j,\ell}r_i.
\]

Writing `m=n+h_j`, the congruences select one **reduced** residue `a_H(q) mod Qq`. With

\[
 \Pi_j=\pi(2N+h_j)-\pi(N+h_j),
\]

define the signed discrepancy by the exact identity

\[
 \#\{N+h_j<m\le2N+h_j:m\in\mathbb P,
                          m\equiv a_H(q)\pmod{Qq}\}
 =\frac{\Pi_j}{\phi(Qq)}+E_j(Qq,a_H(q)).                  \tag{15}
\]

The resulting majorant is its completed main term plus its signed error. The main term is

\[
 \boxed{\quad
 \Pi_j\sum_{\mathbf d,\mathbf e}^{*}
       \frac{\lambda_{\mathbf d}\lambda_{\mathbf e}}{\phi(Q)}
       \sum_{\substack{q\\(q,QZ)=1}}\frac{\rho_q}{\phi(q)}.
 \quad}                                                   \tag{16}
\]

Here endpoints equal 1 in both coefficient vectors, and `*` denotes precisely the compatible core conditions above. The coefficient domain in (16) is independent of the tuple and of `b`. The only remaining shift dependence is the harmless interval total `Π_j=(1+o(1))N/L`, uniformly for logarithmic shifts.

Thus averaging cannot change (16) through an average of small-prime singular factors or through cancellation of incompatible core divisors. The potentially useful signed average is genuinely

\[
 \frac1{|G_N|}\sum_{H\in G_N}
   \sum_{\mathbf d,\mathbf e}^{*}
       \lambda_{\mathbf d}\lambda_{\mathbf e}
       \sum_{\substack{q\\(q,QZ)=1}}\rho_q
                         E_j(Qq,a_H(q)).                  \tag{17}
\]

This retains the modulus, the CRT residue, the divisor coefficients, and their signs. It is not an unmasked pair count. For the full Chen construction the exceptional-prime indicator and, in the switched term, the specified almost-prime sequence must additionally be retained. Formula (17) is the exact error for the simpler valid majorant just defined, not an assertion that these extra Chen dependencies disappear.

For the published fixed functions, (4) is uniform over the good tuples: the source uses maximum-over-residue errors and uniform elementary counting of the CRT solutions. Hence averaging (4), without exchanging weights between tuples, gives exactly the same constants. A growing number of tuples does not multiply a **normalized average's** uniform relative error.

### Check against the actual Chen recipe

M18 **656–677** gives, in the limit of small support parameter, the coefficient

\[
 \begin{split}
 \Omega&=\Omega_1-\Omega_2+\Omega_3,\\
 \Omega_1&=F_{\rm lin}(1/(2a))/(a e^\gamma),\\
 \Omega_2&=\frac1{2a e^\gamma}\int_a^b
                     f_{\rm lin}((1/2-t)/a)\,\frac{dt}{t},\\
 \Omega_3&=2\int_{a<u_1<u_2<u_3<b}
       \omega\left(\frac{1-u_1-u_2-u_3}{u_2}\right)
                           \frac{du_1du_2du_3}{u_1u_2^2u_3},
 \end{split}                                               \tag{18}
\]

with `a=1/7`, `b=3/14`. These letters are sieve exponents, not the desired gap band. All three terms multiply the same `N W^(-1) B^(-K) L_2` and are independent of the tuple geometry. Their safe published combination is 3.99.

There is even a simple rigorous lower check on the coefficient of this *fixed recipe*. The source's expression gives `Ω_1≥4` and `Ω_3≥0`. Also

\[
 \Omega_2=7\int_{1/7}^{3/14}
           \frac{\log(5/2-7t)}{7/2-7t}\,\frac{dt}{t}
 \le\frac72\log^2(3/2)<\frac78.
\]

Consequently `Ω>25/8>2`. This is a lower bound on this upper-bound coefficient, not on the prime-pair count. It does not optimize Chen's method. It establishes the narrower point that **setting all the existing AP error terms to zero does not bring this recipe near 2**. Those errors already contribute `o(N W^(-1) B^(-K) L_2)` at the source's permitted level (M18 **508–519, 606–642**).

## 5. Direct arithmetic attempt beyond the old errors: exact short-shift completion

Fix a core term, the prime anchor `h_j`, and its modulus `Q` from §4. Let the second endpoint be `h_ℓ=h_j+t`, with `t` in an eligible set `T'` from one protected band; write `m=|T'|`. Smooth compatibility with the core is imposed, not assumed away.

Let `q>1` be squarefree, `(q,QZ)=1`. Its prime factors exceed `z`. The eligible shifts have `(t,q)=1`, and distinct members of `T'` are distinct modulo `q`. For the common pools they lie in an interval of length less than `z`.

Let `a_0 mod Q` be the anchor's core residue. Explicitly, `a_0≡b+h_j mod W` and `a_0≡h_j−h_i mod r_i`. With `bar Q` denoting the inverse modulo `q`,

\[
 a_H(q)=a_0+Q[(-t-a_0)\bar Q]_q.                          \tag{19}
\]

Thus the CRT dependence really is linear in the varying shift once the core and common mask are fixed.

Write the anchor numbers as `a_0+Qk`, with `k` in its exact interval `I_Q` of `T_Q=N/Q+O(1)` integers. Set

\[
 A(k)=1_{\mathbb P}(a_0+Qk),\qquad M_Q=\sum_{k\in I_Q}A(k),
\]
\[
 C_q(c)=\sum_{\substack{k\in I_Q\\k\equiv c\ (q)}}A(k),
 \qquad U_q=\{c\pmod q:(a_0+Qc,q)=1\}.
\]

For the range `q<N`, the primes in question exceed every prime divisor of `q`, so `C_q` is zero outside `U_q`. Also `|U_q|=φ(q)`. Define

\[
 D_q(c)=C_q(c)-\frac{M_Q}{\phi(q)}1_{U_q}(c),\qquad
 \widehat D_q(r)=\sum_{c\ (q)}D_q(c)e_q(rc),\qquad
 C_{T'}(r)=\sum_{t\in T'}e_q(rt).
\]

Here `e_q(x)=exp(2πix/q)`. In particular `widehat D_q(0)=0`.

### Proposition 2 — exact average and an evaluated upper bound

Finite Fourier inversion gives

\[
 \boxed{
 \sum_{t\in T'}\left(C_q((-t-a_0)\bar Q)-\frac{M_Q}{\phi(q)}\right)
 =\frac1q\sum_{r\ (q)}e_q(ra_0\bar Q)
                       C_{T'}(r\bar Q)\widehat D_q(r).
 }                                                         \tag{20}
\]

The `φ(q)` is essential: replacing it by `q` would leave the local reduced-class bias in the alleged error. The formula is exact, with the actual CRT inverse.

Distinctness modulo `q` gives

\[
 \sum_{r\ne0}|C_{T'}(r\bar Q)|^2=qm-m^2.
\]

Cauchy–Schwarz therefore proves

\[
 \left|\sum_{t\in T'}D_q((-t-a_0)\bar Q)\right|
 \le\sqrt{\frac mq-\frac{m^2}{q^2}}\,
                   \|\widehat D_q\|_2.                  \tag{21}
\]

Furthermore, Parseval and `C_q(c)≤T_Q/q+1` give the unconditional evaluation

\[
 \begin{split}
 \|\widehat D_q\|_2^2
   &=q\left(\sum_c C_q(c)^2-\frac{M_Q^2}{\phi(q)}\right)\\
   &\le(T_Q+q)M_Q,
 \end{split}
\]

and hence

\[
 \left|\sum_{t\in T'}D_q((-t-a_0)\bar Q)\right|
       \le\sqrt{mM_Q(T_Q/q+1)}.                           \tag{22}
\]

The error against the main term in (15) also includes the exact base-residue discrepancy:

\[
 \begin{split}
 \sum_{t\in T'}E_j(Qq,a_H(q))
  =\sum_{t\in T'}D_q((-t-a_0)\bar Q)
     +\frac m{\phi(q)}\left(M_Q-\frac{\Pi_j}{\phi(Q)}\right).
 \end{split}                                               \tag{23}
\]

Equations (20)–(23) are proved arithmetic identities/estimates, not a proposed prime-pair assumption.

### Quantitative failure of this first direct bound

For `q=p>z` prime, compare the *numerical bound* in (22) with its density main term `m M_Q/(p−1)`. When `M_Q>0`, using `M_Q≤T_Q` gives

\[
 \frac{\sqrt{mM_Q(T_Q/p+1)}}{mM_Q/(p-1)}
 \ge\frac{p-1}{\sqrt{mp}}.
 \tag{24}
\]

Since `m≤M_g≍z/log z`, this is at least a constant times `sqrt(log z)`, not `o(1)`. This is a lower bound on the size of the **available upper-bound expression**, not a lower bound on the actual prime discrepancy. Thus the elementary completion estimate does not reach even the expected density scale. The existing BV estimate handles the old range much better; (22) supplies no extension of its level.

### Exact primitive Gram calculation

For any coefficients `c_t` and a squarefree `q` whose primes exceed `z`, the smooth-difference condition gives

\[
 c_q(t-t')=\mu(q)\quad(t\ne t'),\qquad c_q(0)=\phi(q),
\]

where `c_q` is a Ramanujan sum. Consequently

\[
 \boxed{
 \sum_{\substack{r\ (q)\\(r,q)=1}}
       \left|\sum_{t\in T'}c_t e_q(rt\bar Q)\right|^2
  =(\phi(q)-\mu(q))\sum_t|c_t|^2
                  +\mu(q)\left|\sum_tc_t\right|^2.
 }                                                         \tag{25}
\]

The CRT inverse permutes the reduced frequencies and does not change this norm. For the protected pools, `φ(q)≥min_{p|q}(p−1)>z−1` and `m≪z/log z`. Thus (25) equals

\[
 \phi(q)\sum_t|c_t|^2\left(1+O(1/\log z)\right)
 \tag{26}
\]

uniformly in the coefficients. In particular, the off-diagonal term of this completion cannot halve the diagonal term. The square-root saving in the *number of shifts* in (21) is real; it is not a new power of `N` or a constant-factor improvement of the completed sieve main term.

For a full interval of `O(log N)` shifts rather than the protected pool, the same prime-modulus identity holds whenever `p` exceeds its diameter. At polynomial-size moduli `p≈N^θ`, it reads `p m−m²`, with relative off-diagonal correction `m/p=o(1)`. There are still only logarithmically many shift samples. This observation does not assert that other cancellations jointly involving divisor coefficients and prime discrepancies are impossible.

Most importantly, (25) concerns the shift leg of a completed/Cauchy estimate. It is **not** a theorem controlling the signed sum (17) beyond the published distribution range. Claiming such control would be the missing arithmetic step.

## 6. A sharp calculation for the simpler Selberg-square detector

One might hope to improve the old upper factor just by obtaining a larger support for the extra one-coordinate Selberg square after averaging. Its main-term cost can be calculated exactly.

For a smooth `G` supported on `[0,σ]`, with `G(0)=1`, define

\[
 U_G(x)=\left(\sum_{\substack{d\mid x\\(d,Z)=1}}
                      \mu(d)G(\log d/L)\right)^2.
\]

It is nonnegative and equals 1 at primes near `N`. The completed coefficient multiplying the weighted pair benchmark is

\[
 C_G=\int_0^\sigma |G'(t)|^2\,dt.
\]

Cauchy–Schwarz gives the sharp infimum

\[
 1=|G(0)-G(\sigma)|^2\le\sigma C_G,
 \qquad \inf C_G=1/\sigma,                               \tag{27}
\]

approached by smooth approximations to `1−t/σ`. This is the calculation behind BFM **1613–1625**.

The expanded modulus has size at most

\[
 W\prod_{i\ne j,\ell}[d_i,e_i]\,[u,v]
       \le N^{\eta+2\delta+2\sigma+o(1)}.
\]

At a distribution exponent `θ`, this form of the argument requires `η+2δ+2σ<θ`. Accordingly its limiting minimal coefficient, as the small losses tend to zero, is `2/θ`: **4 at level 1/2 and 2 at level 1**. Even if every relevant AP error vanished, support with `θ≤1` would not give a fixed coefficient below 2 by this square alone. Allowing a different `G` for each tuple and positively averaging does not evade (27), which holds separately for each `G`.

This is a proved limitation of this specific majorant. It does not cover Chen's full switching construction (which already improves 4 at the old level), nor a majorant or detector valid only after a new signed arithmetic averaging argument. No distribution theorem at `θ=1` is assumed here.

## 7. A direct check that the actual averaged weights do not flatten

There is another plausible shortcut after obtaining the common mask: treat the many tuple choices as independent samples and replace the injection sum in (14) by products of empirical means. The following calculation disproves that replacement at main-term scale, even for a genuine product subclass of the source weights.

Work in one of the protected bands `T_g`, write `M=|T_g|`, and use the **uniform probability measure on the actual rows** `N<n≤2N`, `n≡b mod W`. Choose a fixed smooth nonnegative function `f`, supported on `[0,τ]`, with `f(0)=1`; take `τ` small enough for the one- and two-coordinate divisor mass estimates, and include this fixed choice when choosing `η` sufficiently small above. Put

\[
 \xi_f(x)=\sum_{\substack{d\mid x\\(d,Z)=1}}
                     \mu(d)f(\log d/L),\qquad
 a_h(n)=\xi_f(n+h)^2,\qquad c_f=\int_0^\infty f'(t)^2dt.
\]

The elementary BFM mass calculation for one and two coordinates gives, uniformly in these pool points,

\[
 \mathbb E a_h=(c_f+o(1))/B,\qquad
 \mathbb E(a_h a_{h'})=(c_f^2+o(1))/B^2\quad(h\ne h').
 \tag{28}
\]

All within-band differences are `z`-smooth, so no bad tuples are discarded in (28). The functions here are fixed, not functions of the pool size. One can also obtain (28) directly by expanding the squares, counting a single CRT progression with error `O(1)`, and applying BFM **1240–1266**.

At a prime endpoint `ξ_f(n+h)=1`. The one-prime estimate on the same CRT rows therefore proves

\[
 \mathbb E a_h^2\ge\mathbb P(n+h\text{ prime})=(1+o(1))/B.
 \tag{29}
\]

This uses only a **one-prime** estimate, not a pair lower bound. Uniformity in `b` is exactly what the modified BV input supplies.

Set `V=Σ_{h∈T_g}a_h`. Since `M/B→κ_g>0`, (28)–(29) imply

\[
 \mathbb E V\to\kappa_g c_f,
 \qquad
 \liminf_{N\to\infty}\operatorname{Var}(V)\ge\kappa_g.
 \tag{30}
\]

Indeed the off-diagonal sum is `(c_f²+o(1))M(M−1)/B²`, whereas the diagonal is at least `(1+o(1))M/B`; subtracting `(E V)²` leaves the lower bound. Thus the empirical divisor average does **not** approach its mean in relative `L2`: its relative variance has lower limit at least `1/(κ_g c_f²)>0`.

The discrepancy between averaging with and without replacement is especially explicit. Define

\[
 A_2=\frac{\sum_{h\ne h'}a_ha_{h'}}{M(M-1)},\qquad
 R_2=\left(\frac1M\sum_ha_h\right)^2,
 \qquad D=\sum_ha_h^2.
\]

Exactly,

\[
 A_2=\frac{V^2-D}{M(M-1)},\qquad
 R_2-A_2=\frac{MD-V^2}{M^2(M-1)}\ge0.
 \tag{31}
\]

Equations (28)–(29) then give

\[
 \mathbb E A_2=(c_f^2+o(1))B^{-2},\qquad
 \liminf_{N\to\infty}B^2\mathbb E(R_2-A_2)\ge1/\kappa_g.
 \tag{32}
\]

So the repeated-coordinate error is **at least of the order of the genuine two-coordinate mass**, not `o(B^(-2))`, despite a repetition probability of only `1/M`. The missing factor is `B/M`, which tends to a positive constant, not zero.

This is not a claim about every optimized Maynard test function. It is a rigorous countercheck against flattening/independent-sampling manipulations of (12)–(14). It is distinct from transferring an ordinary pair estimate through a rare vacancy mask: all expectations in (28)–(32) are on the retained CRT rows, with explicit divisor kernels.

## 8. What has and has not been obtained

The first serious tuple-averaging failure, changing the CRT mask with the tuple, **has been repaired** for a substantial family in any prescribed two-band geometry. The repair keeps the exact source modulus, omits the exceptional prime, and preserves a valid route from simultaneous occupancy to global consecutivity.

The subsequent arithmetic calculations give no improvement of the prime-pair factor:

- At the old support/distribution level, averaging the uniform source estimates gives the same mass, first moment, and pair constant. Formula (16) explains why at the divisor level.
- The fixed Chen recipe's main terms survive unchanged even if its already-negligible errors are deleted; (18) even gives an elementary lower bound `Ω>25/8` for that recipe's coefficient.
- The direct short-shift attempt gives (20)–(23), but its unconditional elementary evaluation is larger than its density main term by at least order `sqrt(log z)` in (24).
- The exact Gram calculation identifies what off-diagonal shift cancellation actually contributes in that completion. It does not estimate the additional signed prime/divisor correlation (17).
- Products of average kernels cannot replace tuple averages at the required scale, as (30)–(32) show.

The existing symmetric two-group occupancy certificate therefore remains the one in `InitialIntervalAmplificationAttempt.md`, with `A=3.99`, not a new coefficient. Its already checked negative quadratic optimization is not repeated as a purported new obstruction. I have obtained neither an averaged estimate below 2 in that normalization nor a different detector that forces both groups occupied.

If such simultaneous occupancy were proved, the extrema of the two protected pools would be globally consecutive primes at heights `N+O(log N)` through `2N+O(log N)`. For their global prime index `j`, PNT gives `log j/log N→1`, so strict interior margins would deliver arbitrarily late gaps in the original band normalized by `log j`. There is no remaining scale or consecutivity ambiguity in this construction; **simultaneous prime occupancy is not proved**.

## 9. Verification

`python3 Submission/check_averaged_pair_weight.py` passes:

- 304 Ramanujan/Parseval/CRT-inverse cases;
- 66 exact AP-discrepancy and `L2` cases, with arbitrary nonnegative data on reduced classes;
- 54 compatible/incompatible divisor CRT cases;
- 287 separable-kernel, injection-average, and diagonal identities;
- 3,720 exact rational Selberg-energy cases;
- 18 growing-protected-set reserve-cover cases satisfying the finite capacity hypotheses.

The reserve test takes a survivor set satisfying the capacity hypothesis as input. It does not simulate the asymptotic preliminary sieve. The Fourier checks independently test the CRT signs and the distinction between `q` and `φ(q)`. None of these finite tests certifies an asymptotic prime-distribution theorem or searches for prime gaps. The proofs and the cited uniform source estimates supply those parts of the deductions.

The SHA-256 of `Submission/Spec.lean` was checked both before and after the work and remained

`47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123`.

No Lean file was changed, and no theorem or negation containing `sorry` was used as input.
