# Summed pressure: paying the adaptive-certificate entropy cost

## Exact status

**The requested completion is not obtained.** Neither summed EL nor a positive lower bound for `Z_infinity` is proved. In particular, `R(Q_d)=O(2^d)` remains unsolved by this work. No specification or Lean file was changed.

This is one positive entropy-counting chain, not a new bad-sector construction. Its new quantitative conclusion is that, at the selected linear scales, **the actual full integral initial packing ensemble retains the prescribed surplus even after paying for the entire catalogue of adaptive full-parity Hall certificates**. Precisely, in the notation below,

\[
 \boxed{\quad
 \log Z_0+s r\log q_k-\log\binom{N+h/2}{h/2-1}
       \ge \frac{k h}{5}.
 \quad}                                                    \tag{A}
\]

Consequently, for sufficiently large `d` at fixed `K`,

\[
 \boxed{\quad
 \left(\frac{Z_0}{\binom{N+h/2}{h/2-1}}\right)^{1/s}q_k^r
       \ge h^2\exp(kb/10).
 \quad}                                                    \tag{B}
\]

These are proved inequalities for `Z_0`, not assertions about `Z_infinity`. The argument also gives an exact conditional-entropy localization statement for a selected certificate fibre. It does **not** interchange a sector infimum and a sector sum. The final section identifies the one step not supplied by this chain.

The pressure program was read in full, as were Sections 1–2 of `CubeEdgePressureResolutionAttempt.md` and Sections 5–6 of `CubeConflictDRCAttempt.md`. Their actual-minimizer convention, full injection convention, and warnings about common prices are retained.

## 1. Setup and the exact size of the adaptive catalogue

Use the program's notation

\[
 h=2^d,\qquad b=2^k,\qquad r=d-k,\qquad s=2^r=h/b,
 \qquad m=h/2.
\]

There are `s` **whole** `Q_k` blocks. By contrast, `E,O` below are the parity classes of the **full** `Q_d`, each of size `m`. They are not the outer parity classes of `Q_r`.

Let `A=A_(lambda*)` be the actual finite `Phi_(k+1)` minimizer on the majority graph `G`. Thus `A>0` exactly on the edges of `G`. Write

\[
 M=N^b t_k(A),\qquad q=q_k=t_{k+1}(A)/t_k(A)^2.
\]

For an actual injective block `g`, put

\[
 w(g)=\prod_{uv\in E(Q_k)}A(g(u),g(v)).
\]

Let `Omega_0` consist of all globally injective placements of the `s` labelled blocks with positive internal weight, and put

\[
 w_0(\phi)=\prod_{i=1}^s w(\phi_i),\qquad
 Z_0=\sum_{\phi\in\Omega_0}w_0(\phi),\qquad
 \pi_0(\phi)=w_0(\phi)/Z_0.                                \tag{1.1}
\]

This is the **full** initial integral packing ensemble, not a chosen orbit or a product law with collisions ignored.

For an injection `f:E -> [N]`, define the hard full-edge lists

\[
 L_y(f)=\{v\notin\operatorname{im}f:
                  A(f(x),v)>0\text{ for every }x\sim y\},
       \qquad y\in O.                                    \tag{1.2}
\]

Every one of the `d` neighbours is tested. Since the opposite parity has no internal edges, a matching saturating these lists is exactly an injective full extension of `f`.

### Lemma 1 — the exact Hall-certificate catalogue

Assume `N>=h`. Every nonextendible `f` has a certificate

\[
 \varnothing\ne I\subseteq O,\qquad
 S\subseteq[N]\setminus\operatorname{im}f,\qquad
 |S|=|I|-1,\qquad L_y(f)\subseteq S\quad(y\in I).          \tag{1.3}
\]

The number of possible pairs `(I,S)`, using the whole host as the catalogue and allowing pairs that do not occur, is exactly

\[
 L_{N,m}:=\sum_{i=1}^m\binom mi\binom N{i-1}
                =\binom{N+m}{m-1}.                       \tag{1.4}
\]

For `m>=2`, with `C=N/h>=1`,

\[
                  \log L_{N,m}\le\frac h2\log(6eC).        \tag{1.5}
\]

**Proof.** Hall gives a nonempty `I` with `|union_(y in I) L_y(f)|<=|I|-1`. There are at least `m` vertices outside `im f`; hence the union can be enlarged, still outside `im f`, to a set `S` of size exactly `|I|-1`.

For the identity, set `j=i-1` and use

\[
 \sum_{j=0}^{m-1}\binom m{m-1-j}\binom Nj
                      =\binom{N+m}{m-1}.
\]

Finally, `binom(a,t)<=(ea/t)^t` and

\[
 \frac{N+m}{m-1}
       =\frac{(2C+1)m}{m-1}\le 2(2C+1)\le6C
\]

prove (1.5). No price vector, row-by-row list encoding, or boundary embedding is included in this code. QED.

The saving is relevant: the catalogue costs `O_C(h)` bits in natural-log units, not `O(dh)`. This counts **all** Hall certificates, not only a preselected structured family.

## 2. Selecting a certificate from the full initial ensemble

Suppose temporarily that `Z_infinity=0`. Every parity sector having positive `pi_0` weight then has a certificate (1.3). Choose one deterministically, for example lexicographically, and denote it by

\[
                     \mathcal C=\mathcal C(\phi|_E).
\]

This random variable takes at most `L_{N,m}` values. Define

\[
 Z_{0,c}=\sum_{\phi:\mathcal C=c}w_0(\phi),\qquad
 p_c=Z_{0,c}/Z_0,\qquad \rho_c=\pi_0(\,\cdot\mid\mathcal C=c).
\]

At least one `c` satisfies

\[
 Z_{0,c}\ge Z_0/L_{N,m},\qquad
 D(\rho_c\Vert\pi_0)=-\log p_c\le\log L_{N,m}.            \tag{2.1}
\]

The conditional extension law **given the whole pinned parity** is unchanged by this conditioning: `mathcal C` is a function of that parity. Consequently (2.1) is precisely a sector-selection cost; it is not a cost assigned to a different or relaxed extension ensemble.

Its weighted entropy is exactly

\[
 H(\rho_c)+\mathbb E_{\rho_c}\log w_0=\log Z_{0,c}.        \tag{2.2}
\]

Also `w_0<=1` gives

\[
                      H_\infty(\rho_c)\ge\log Z_{0,c}.    \tag{2.3}
\]

These are assertions about laws of **all `h` original labels**, injective in every outcome.

### Lemma 2 — the packing-conditioning term cannot be silently removed

Let `nu_k` be the weighted small-cube **homomorphism** law, with normalizer `M`, and put

\[
 \mu=\nu_k^{\otimes s},\qquad
 \Lambda=\log(M^s/Z_0)=-\log\mu(\Omega_0).
\]

Then `pi_0=mu(. | Omega_0)`. For every nonempty certificate fibre,

\[
 \boxed{\quad
 \sum_{i=1}^sD((\rho_c)_i\Vert\nu_k)
          +\operatorname{TC}(\rho_c)
       =\Lambda-\log p_c,
 \quad}                                                    \tag{2.4}
\]

where `TC(rho)=sum_i H(rho_i)-H(rho)>=0` is total correlation. Averaging gives

\[
 \sum_i\mathbb E_cD((\rho_c)_i\Vert\nu_k)
       +\mathbb E_c\operatorname{TC}(\rho_c)
                   =\Lambda+H(\mathcal C).                \tag{2.5}
\]

**Proof.** On `Omega_0`, `pi_0/mu=exp(Lambda)`. Thus

\[
 D(\rho_c\Vert\mu)=D(\rho_c\Vert\pi_0)+\Lambda
                         =-\log p_c+\Lambda.
\]

Expanding relative entropy against the product measure `mu` gives (2.4); average over `c` for (2.5). All internal edge weights are included in `nu_k` and in `pi_0`. QED.

In particular, applying the small-cube KL comparison directly to the already conditioned packing law would omit `Lambda`. The next section pays for `Lambda` and `H(mathcal C)` together, rather than assuming either is negligible.

## 3. The actual integral surplus pays for the entire catalogue

The following restrictions are permitted at the actual selected scales: enlarge `C_0(K)` if necessary, and assume

\[
 K\ge512,\qquad C=N/h\ge K,\qquad
 1\le k\le d/4,\qquad k\ge64d/K.                          \tag{3.1}
\]

The majority/minimizer prerequisites give

\[
                  p=p(A)\ge\frac12-\frac2K.
\]

Put

\[
 \rho=p-2/C\ge\frac12-\frac4K>\frac14,
 \quad
 \eta=\frac{\binom b2}{(N-h)\rho^k},
 \quad
 B=(1-\eta)(N-h)^b\rho^{kb/2}.                           \tag{3.2}
\]

We use, without re-proving it, the weighted residual injective-block estimate from Section 2 of the pressure program: after any deletion of at most `h` vertices, the actual internal block partition is at least `B`. Here its hypotheses hold uniformly, since

\[
 \eta\le\frac{2^{4k-d}}{2(C-1)}
                  \le\frac1{2(C-1)}<\frac12.              \tag{3.3}
\]

Thus the proved initial packing estimate and weak norming give

\[
                         Z_0\ge B^s,
            \qquad q\ge a_k(A)^b\ge\rho^b.              \tag{3.4}
\]

No estimate for a boundary-conditioned block is used in (3.4).

### Theorem 3 — certificate-subtracted, globally integral surplus

Under (3.1),

\[
 \boxed{\quad
 \log Z_0+s r\log q-\log L_{N,m}\ge kh/5.
 \quad}                                                    \tag{3.5}
\]

Equivalently, in terms of the product-law packing cost,

\[
 s\log(Mq^r)-\Lambda-\log L_{N,m}\ge kh/5.                \tag{3.6}
\]

If additionally `kb>=20 log h`, then

\[
 \left(Z_0/L_{N,m}\right)^{1/s}q^r
                       \ge h^2e^{kb/10}.                 \tag{3.7}
\]

The extra condition in (3.7) holds eventually throughout the selected interval, because `k>=64d/K` for fixed `K`.

**Proof.** Since `K>=512`,

\[
 \log\rho\ge-\log2+\log(1-8/K)
                  \ge-\log2-9/K.                         \tag{3.8}
\]

Indeed `-log(1-x)<=x/(1-x)` and `8/(1-8/K)<=512/63<9`.
Using `1-eta>=1/2`, (3.4), and `s=h/b`, we obtain

\[
\begin{aligned}
 \frac1h(\log Z_0+s r\log q)
 &\ge \log(N-h)+(d-k/2)\log\rho-\frac{\log2}{b}\\
 &\ge \log(C-1)
       +\left(\frac{\log2}{2}-\frac9{64}\right)k
       -\frac{\log2}{b}.                                 \tag{3.9}
\end{aligned}
\]

The last line uses `9d/K<=9k/64` and drops the additional nonnegative `9k/(2K)` term. Subtract (1.5). With `C>=512` and `b>=2`, the remaining constant term is nonnegative:

\[
\begin{aligned}
 \log(C-1)-\tfrac12\log(6eC)-\frac{\log2}{b}
 &\ge \tfrac12\log C-\tfrac32\log2-\tfrac12\log6-\tfrac12\\
 &\ge 3\log2-\tfrac12\log6-\tfrac12>0.                   \tag{3.10}
\end{aligned}
\]

Finally,

\[
                  \frac{\log2}{2}-\frac9{64}>\frac15.
\]

For an elementary exact check, the positive series for `log 2` gives
`log 2 >= 2(1/3+1/81)=56/81 > 109/160`.
This proves (3.5). Identity (3.6) is the definition of `Lambda`.
Dividing (3.5) by `s` yields `kb/5`; if `kb>=20 log h`, this is at least `2 log h+kb/10`, proving (3.7). QED.

Thus (3.7) preserves **the same type of `h^2 exp(kb/10)` reserve as in the program**, but replaces the raw one-block count `M` by the geometric mean of an actual global integral partition after paying for **every possible adaptive Hall certificate**.

Under the provisional assumption `Z_infinity=0`, choose the fibre in (2.1). Equations (2.2), (3.5), and (3.7) give

\[
 H(\rho_c)+\mathbb E_{\rho_c}\log w_0+s r\log q
                                                \ge kh/5,\tag{3.11}
\]

and, eventually,

\[
                         Z_{0,c}^{1/s}q^r
                                  \ge h^2e^{kb/10}.       \tag{3.12}
\]

So a hypothetical failure cannot be addressed by saying that *selecting an adaptive certificate has consumed the entropy reserve*. It has not: one fixed certificate fibre still has the complete reserve (3.12), in a law of genuine initial packings.

## 4. Localization of that entropy loss along actual block exposures

This gives more than a large total support count.

### Lemma 4 — few block transitions can pay a large selection cost

Order the `s` whole blocks arbitrarily. For a positive-probability history `u=(X_1,...,X_(i-1))` under a selected fibre law `rho_c`, define

\[
 D_i(u)=D\bigl(\rho_c(X_i\mid u)\Vert\pi_0(X_i\mid u)\bigr).
\]

Then

\[
              \sum_{i=1}^s\mathbb E_{\rho_c}D_i
                 =-\log p_c\le\log L_{N,m}.              \tag{4.1}
\]

For each such history, the **current conditional law**, not an old unconditional marginal, satisfies

\[
 H_{\rho_c}(X_i\mid u)
       +\mathbb E_{\rho_c}[\log w(X_i)\mid u]
                                    \ge\log B-D_i(u).    \tag{4.2}
\]

Consequently

\[
 \mathbb E_{\rho_c}\#\{i:D_i(X_{<i})>kb/20\}
        \le \frac{20\log L_{N,m}}{kb}
        \le s\,\frac{10\log(6eC)}{k}.                    \tag{4.3}
\]

At every history outside this exceptional set, the conditional weighted block entropy retains

\[
 H_{\rho_c}(X_i\mid u)
  +\mathbb E_{\rho_c}[\log w(X_i)\mid u]+r\log q
                                                   \ge3kb/20. \tag{4.4}
\]

For fixed `C`, the expected exceptional fraction in (4.3) tends to zero at the selected scales. No assertion about every history after a further conditioning is made.

**Proof.** Equation (4.1) is the chain rule for relative entropy against the *actual* reference law `pi_0`, combined with (2.1).

First condition `pi_0` on **all blocks other than `i`**. Its free-block law is exactly

\[
 \frac{w(g)\,1_{\operatorname{im}g\cap S=\varnothing}}
      {\operatorname{inj}(Q_k,A[V\setminus S])},
\]

where `|S|=h-b`. The denominator is at least `B`, by the cited residual estimate. Hence its probability at `g` is at most `w(g)/B`. Averaging over unexposed outside blocks preserves this bound:

\[
                         \pi_0(X_i=g\mid u)\le w(g)/B.   \tag{4.5}
\]

Expanding `D_i(u)` and using (4.5) proves (4.2). All terms with positive `rho_c` probability have `w(g)>0`, so the logarithms are finite.

Markov's inequality for the nonnegative quantities `D_i` proves (4.3). The same calculation as (3.9), before dividing a whole packing into `s` blocks, gives

\[
 \log B+r\log q
   \ge b\left[\log(C-1)
        +\left(\frac{\log2}{2}-\frac9{64}\right)k\right]-\log2
   \ge kb/5.
\]

Subtracting `kb/20` in (4.2) proves (4.4). QED.

This is a localized statement about the high-entropy law selected **from the full initial ensemble**. It neither transfers the small-cube edge-flux certificate through conditioning nor replaces sector-dependent row capacities by expected column loads.

## 5. Where the complete mathematical chain still stops

The forced inequalities (3.5)–(3.7), the selection law (2.1), and the history bounds (4.1)–(4.4) are the results obtained. They pay the two entropy charges that cannot be omitted: global packing conditioning and the choice of an adaptive certificate.

They do **not** put the remaining outer edges into that law. In particular, `r log q` in (3.11) or (4.4) is an entropy **budget**, not the logarithm of a proved conditional probability of all `r` external incidences. Replacing it by such a probability would be exactly the missing lifting step.

More explicitly, a block exposed at a history in Lemma 4 has a high-entropy conditional law on actual internally valid blocks. The lemma gives no lower bound for its mass on the simultaneous coordinate domains

\[
 \{g:g(a)\in\bigcap_{x\sim y}N_G(F_x(a))
                    \text{ for every required label }a\}.
\]

Even the fixed certificate selected in Section 2 still constrains these overlapping neighbourhood intersections. Freezing its *code* does not make those constraints into a common vertex or edge price on the unconditional small-cube law.

The small norm increment and actual-minimizer optimality have **not** been converted into an estimate for that missing conditional mass. In the proved surplus calculation, the minimizer is used for its density consequence; the upper bound on `(k+1)Delta_k` supplies no additional justified exclusion here. I do not claim otherwise. In particular, the previously proved small-cube KL comparison is not propagated through either the whole-packing conditioning or the Hall-fibre conditioning.

Thus this report does not assert a new sufficient hypothesis and then treat it as a result. It proves an actual, forced certificate-subtracted global entropy inequality and stops before the unproved outer-edge/capacity implication. There is no lower bound on `Z_T` for all `T`, no sublinear-in-`T` pressure bound at large `T`, and no proof of `Z_infinity>0`.

## 6. Executable audit and integrity

Run from `/workspace/leanproject`:

```sh
python3 -u Submission/check_cube_summed_pressure_completion.py
```

Recorded output: `Submission/CubeSummedPressureCompletionVerification.txt`.

The audit checks:

* the exact Vandermonde catalogue count at **1,110** parameter pairs;
* Hall certificates versus actual matchings for **all 32,768** Boolean `3 by 5` list matrices: **29,206** are matchable and **3,562** have certificates;
* **20** small weighted host cases, enumerating **3,488** positive configurations of the *full integral* two-block packing ensemble;
* **47** nonempty certificate fibres and **346** conditional-history entropy inequalities, including the unchanged extension law given the full parity and the past-conditioned bound (4.5);
* **324** selected-scale parameter choices for the analytic, certificate-subtracted lower bound. The smallest audited excess over `k/5`, normalized by `h`, is **1.74977292452**.

Counts, support tests, and finite weighted partitions use integers or rational numbers. Logarithmic entropy identities use floating-point arithmetic only after those exact partitions are formed. The small host cases audit the algebra and the correct conditioning; they are **not** tests of the large-`C`, selected-scale theorem. The all-dimensional proof of (3.5) is the analytic proof above, not the finite loop.

Unchanged `Submission/Spec.lean` SHA-256:

```text
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

**Final status: adaptive-certificate entropy paid; summed EL and positive full injection still unproved.**
