# Overlap consistency of the common-mask Maynard moments

## Result and scope

**Erdős #5 is not proved.** There is, however, an overlap-consistent obstruction to the **entire leading fixed-complexity, log-smooth divisor-kernel moment system** supplied by the mass and one-prime calculations, not merely a separate model for each tuple.

The construction below uses one hidden bit for the whole pair of pools. Every label carries a full auxiliary integer factorization, from which *all* its kernels, mixed kernels, and prime flag are defined. Restrictions to overlapping tuples are automatically consistent. It matches the source's leading mass and one-prime moments throughout the permitted support ranges, and gives within-pool prime factors `2^(r-1)` and zero cross-pool primes. Thus polarization, shared Gram matrices, overlapping tuples, and all fixed-order products within the distribution budget do not by themselves force simultaneous occupancy.

This is a model of the **asymptotic moment identities**, not of actual common translates `n+h`. In particular it is not a counterfeit construction of an integer row with a prescribed prime pattern, and does not disprove the conjecture. Exact residue observations at individual primes, the full growing small-divisor sigma-field, and arbitrary growing-complexity tests are not being assigned their actual joint law by this model. Those distinctions are essential, not harmless omissions to be filled by a monotone-class argument.

A genuine additional consequence is a stronger diagonal bound: for a fixed primitive kernel supported in `[0,a]`, `f(0)=1`, and `4a+2 eta<1`, its common-row fourth moment is at least `(2+o(1))/B`. Consequently the variance lower bound for its pool sum can be strengthened from `kappa` to `2 kappa`. This increases the obstruction to concentration; it does not create cross-pool primes.

No Lean theorem with `sorry` was used. `Submission/Spec.lean` was not changed.

## 1. Source audit and support bookkeeping

Local sources checked directly:

* **BFM:** `/corpus/src/1404.5094/banks-freiberg-maynard-limit-points-of-normalized-prime-gaps-arXiv.tex`.
  * 1161–1178: fixed dimension and functions, `2 delta+2 epsilon<1/2`, and `W<N^(2 epsilon)`.
  * 1180–1238: divisor coefficients, primitive functions, support, and `B`.
  * 1240–1266: the *bilinear* divisor identity, with either `[d,e]` or `phi([d,e])` in the denominator; constant `integral f' g'` in each coordinate.
  * 1280–1351: `I,J,L`, mass, one-prime moment, and the pair upper bound `4+O(delta)`.
  * 1354–1414: elementary CRT counting and its support-dependent error.
  * 1416–1504: freezing the prime coordinate, the reduced AP residue, divisor-weighted BV error, and the factors `f(0)g(0)`.
  * 1506–1625: the auxiliary square and its derivative energy. The local TeX has typographical inconsistencies involving `log R` and the final support description; the displayed support/modulus argument is what is used here, not an inference of a larger level from those typos.
* **M18:** `/corpus/src/1811.03008/limitp2.tex`.
  * 174–189: expected pair normalization, `3.99`, and the significance of a multiplier below 2.
  * 218–225: exceptional prime and BV on multiples of the smooth modulus, with maximum over reduced residues.
  * 353–390: exact weights, smooth differences, CRT hypothesis, and `3.99+O(delta)`.
  * 394–399: prime-coordinate freezing, including the exceptional-prime indicator when the frozen weight is used away from primes.

Keep the pools and common mask of `AveragedPairWeightAttempt.md`. Write

\[
 L=\log N,\quad z=\eta L,\quad W=\prod_{p\le z,\ p\ne Z}p,
 \quad B=(\phi(W)/W)L,
 \quad \mathbb E_R=\text{uniform mean on }\{N<n\le2N:n=b\pmod W\}.
\]

The pool labels lie in an interval of length `O(z)`, all are protected, and `M_g/B -> kappa_g>0`. Define

\[
 P_h(n)=1_{\mathbb P}(n+h),\qquad
 X_h(f)=\sum_{\substack{d\mid n+h\\(d,Z)=1}}\mu(d)f(\log d/L).
 \tag{1}
\]

On these rows divisors containing a prime of `W` contribute nothing. All functions and the number of their occurrences in any test are fixed before taking `N -> infinity`. “All tests” below means every such fixed test, **not** a uniform estimate over a function class or a dimension growing with `N`.

There is also a parameter-order caveat: BFM 790–799 makes the admissible small-mask parameter depend on the desired BV log saving and the level slack. For any fixed finite collection of tests it can be chosen small enough once, before constructing the common mask. At a preassigned `eta`, only the one-prime identities for which that BV hypothesis holds are asserted arithmetically. The model below satisfies even the larger formal collection specified just by the support inequalities; this strengthens the non-implication result, but does not assert a new uniform BV theorem.

## 2. What overlaps genuinely add

### 2.1 Expand after merging labels, not before

A product of features from several overlapping tuples is a finite sum of monomials

\[
 A=\prod_{h\in H}\prod_{v=1}^{m_h} X_h(f_{hv}).             \tag{2}
\]

If `f_hv` has support in `[0,a_hv]`, put `rho=sum a_hv`. A repeated label remains **one** divisor coordinate with several kernels. For a divisor choice put

\[
 q_h=[d_{h1},\ldots,d_{hm_h}],\qquad
 c(\mathbf d)=\prod_{h,v}\mu(d_{hv})f_{hv}(\log d_{hv}/L).
\]

For a smooth-difference union, elementary CRT gives

\[
 \mathbb E_R A
 =\sum_{\mathbf d}^{*}\frac{c(\mathbf d)}{\prod_hq_h}
   +O(N^{\rho+2\eta-1+o(1)}),                              \tag{3}
\]

where `*` requires the `q_h` and `WZ` to be pairwise coprime. The safe sufficient mass condition is `rho+2 eta<1`.

For one prime anchor `j`, first delete **every** kernel occurrence at `j`, replacing it by its value at zero. Let `rho_j` be the remaining support sum, `H'=H\{j}` (or `H'=H` if the anchor was external), and
`c_j=product_v f_jv(0)` (empty product 1). Retain the interval prime-density factor

\[
 \beta_{N,j}=\frac W{\phi(W)}
       \frac{\pi(2N+h_j)-\pi(N+h_j)}N
       =\frac{1+O(1/L)}B.
\]

Then the same BV argument as BFM 1416–1504 gives

\[
 \mathbb E_R P_j A
 =c_j\beta_{N,j}
   \sum_{\mathbf d\text{ on }H'}^{*}
             \frac{c(\mathbf d)}{\prod_{h\in H'}\phi(q_h)}
   +o_A(L^{-A})                                           \tag{4}
\]

for any prescribed fixed error exponent `A`, provided `rho_j+2 eta<1/2` with fixed slack and the small-mask parameter is chosen as in the modified BV theorem. Kernels at the prime anchor need only have support strictly below 1 for the freezing identity. Their support does **not** consume the AP modulus after freezing.

The factor `beta_(N,j)` can be replaced by `1/B` in the leading identities (7), but not in an arbitrary-log-power error statement: the logarithmic integral has secondary terms. Bounded fixed coefficients and the fixed number of divisor variables give a divisor-function multiplicity at each modulus; the same Cauchy–Schwarz/BV estimate used in the source applies. This is an extension of its proof, not a new prime-pair theorem.

One need not lose consistency when two good tuples have a union that is not good. For that union use the exact compatibility conditions, the denominator `lcm_h q_h` in (3), and the corresponding reduced-residue test in (4). A prime exceeding `z` can affect the usual local factor only if it divides a difference. For a fixed number of distinct labels in an `O(z)` interval there are `O_H(1)` such primes, all greater than `z`; their factors are `1+O_H(1/p)`. Thus they change the smooth-kernel leading constants by `1+o(1)`, uniformly in the labels. Incompatible congruences or nonreduced prime residues contribute zero. The elementary counting and BV modulus bounds are unchanged. This extends the **mass and one-prime leading identities** to all fixed unions from these pools. It does not extend M18's pair theorem without its stated hypotheses.

### 2.2 The common local functional, including repeated kernels

For clarity, the general local constant in (3)–(4) can be specified without confusing it with a product of pair constants. Use a smooth compact extension of each `f_v` to the real line and an inverse Laplace representation
`f_v(t)=integral hat(f_v)(s) exp(-st) ds/(2 pi i)` on `Re s=1`. Define

\[
 \begin{split}
 K_m(s_1,\ldots,s_m)
   &=\prod_{\varnothing\ne S\subseteq[m]}
           \left(\sum_{v\in S}s_v\right)^{(-1)^{|S|+1}},\\
 D_m(f_1,\ldots,f_m)
   &=\int\cdots\int\prod_v\widehat f_v(s_v)
                      K_m(\mathbf s)\prod_v\frac{ds_v}{2\pi i}.
 \end{split}                                               \tag{5}
\]

This does not depend on the extension on negative arguments. In particular

\[
 D_1(f)=-f'(0),\qquad D_2(f,g)=\int_0^\infty f'(t)g'(t)\,dt.
 \tag{6}
\]

Here is the Euler-product verification of (5), including the reason overlaps cause no unspecified new constants. At a single prime the one-site divisor sum with denominator `q` has factor

\[
 1+\frac{\prod_v(1-p^{-s_v/L})-1}{p}.
\]

Extract the zeta factors
`product_(nonempty S) zeta(1+sum_(v in S)s_v/L)^((-1)^|S|)`.
Their total pole order is `-1`, giving `B^(-1) K_m`. The remaining factors at `p>z` are `1+O_m(p^(-2))`; primes of `W` supply the factor `W/phi(W)`, and excluding `Z` changes the answer by `1+o(1)`. Replacing `q` by `phi(q)` has the same leading factors. Cross-coordinate coprimality also changes only the `O(p^(-2))` terms. The finitely many bad-difference primes described above are harmless `1+O(1/p)` factors. For example, truncate the imaginary variables at `L^(1/4)`. On this range the zeta expansions and the removal of the primes of `W` are uniform, since `L^(1/4) log z/L -> 0`. Absolute Euler products grow at most as a fixed power of `L`; rapid transform decay makes the discarded tails negligible even after multiplication by the required power of `B`. This proves the fixed-function extension of the bilinear divisor lemma.

Consequently, with `d=|H|` and `d'=|H'|`, the additive leading identities are

\[
 \begin{split}
 \mathbb E_R A
   &=B^{-d}\prod_{h\in H}D_{m_h}(\mathbf f_h)+o(B^{-d}),\\
 \mathbb E_R P_j A
   &=c_j B^{-(d'+1)}\prod_{h\in H'}D_{m_h}(\mathbf f_h)
                                      +o(B^{-(d'+1)}).
 \end{split}                                               \tag{7}
\]

These are additive statements even when a leading constant vanishes. They include polarization, mixed primitive functions, products of overlapping weights, and the diagonal corrections from repeated labels. They describe the full leading fixed-product system from the displayed divisor expansion and the counting/BV budgets; no completeness claim about all conceivable analytic estimates is intended.

The obstruction below realizes (7). It is **not** claimed to reproduce the lower-order finite-`N` completed divisor sums in (3)–(4) to arbitrary-log-power accuracy. Those formulas are retained to distinguish the stronger arithmetic information from its leading moment projection. A proof exploiting such lower-order corrections is not excluded by this result.

### 2.3 Gram constraints are real, but are not conditional independence

For any finite family of allowed features `A_u`, the matrices

\[
 G_{uv}=\mathbb E_R A_uA_v,\qquad
 G^{(j)}_{uv}=\mathbb E_R P_j A_uA_v
\]

satisfy `0 <= G^(j) <= G` as quadratic forms. Products must obey the relevant support budget **entry by entry**, and applying a quadratic-form identity to a linear combination requires its diagonal entries too. The entries between `P_i A_u` and `P_j A_v` involve two primes and are not fixed by (7).

For a shared one-site family supported in `[0,a]`, the limiting kernel Gram form is `D_2(f,g)`. Removing an atom of size `q/B` at the prime evaluation `f -> f(0)` requires

\[
 \int |f'|^2\ge q|f(0)|^2.
\]

But `|f(0)|^2 <= a integral |f'|^2`. Thus a **double prime atom** is compatible with all these Gram forms whenever `a<=1/2`. Its exclusion by this test would require square support beyond the unconditioned counting budget. Under a one-prime condition, the second site's square has the stricter budget `2a+2 eta<1/2`, so there is still more room. There is no inconsistent choice of a different Gram matrix for each kernel in the model below.

## 3. A global, factorization-marked parity model

### 3.1 Parity neutrality for logarithmically rough auxiliary integers

Let `U_N` be the uniform law on

\[
 \mathcal U_N=\{N<m\le2N:(m,W)=1\},
\]

and let `lambda_L(m)=(-1)^(Omega(m))` denote Liouville (not the Maynard coefficients). Let `U_N^-` and `U_N^+` be its conditional odd- and even-parity laws. For any fixed product

\[
 T(m)=\prod_{v=1}^r\sum_{\substack{d\mid m\\(d,Z)=1}}
                         \mu(d)f_v(\log d/L),
 \quad \rho=\sum_v a_v,\quad \rho+2\eta<1,
\]

one has, for every fixed `A`,

\[
 \mathbb E_{U_N}\lambda_L T=o_A(L^{-A}),\qquad
 \mathbb E_{U_N^\pm}T=\mathbb E_{U_N}T+o_A(L^{-A}).       \tag{8}
\]

**Proof.** The standard zero-free-region consequence of PNT gives
`sum_(m<=x) lambda_L(m) << x exp(-c sqrt(log x))`, with a weaker positive constant sufficient here. For `q<=N^rho`, `(q,W)=1`, complete multiplicativity and inclusion–exclusion give exactly

\[
 \sum_{\substack{N<m\le2N\\q\mid m\\(m,W)=1}}\lambda_L(m)
 =\lambda_L(q)\sum_{e\mid W}\mu(e)\lambda_L(e)
       \sum_{N/(qe)<u\le2N/(qe)}\lambda_L(u).
\]

Since `W<N^(2 eta)` and there is fixed slack, every inner interval has scale at least a fixed positive power of `N`. Therefore its absolute value, after summing over `e`, is

\[
 \ll (N/q)\exp(-c'\sqrt L)\prod_{p\mid W}(1+1/p).
\]

For the expanded fixed product, the sum of absolute coefficients divided by their lcm is `O_r(L^(2^r-1))`: relax the support restrictions and use local factors `1+(2^r-1)/p`. Also `|U_N|~N phi(W)/W`; elementary inclusion–exclusion has error `2^(pi(z))=N^o(1)`. This proves the first estimate. Its case `T=1` gives parity probabilities `1/2+o_A(L^(-A))`, proving the second. ∎

Importantly, this removes primes only up to **`z=eta log N`**. It does not assert Liouville cancellation after removing primes up to a fixed power of `N`; that assertion is false in the relevant rough regimes.

The same elementary divisor count and Euler calculation as in §2 show that these auxiliary expectations have the local constants `B^(-1) D_r`. Moreover

\[
 \Pr_{U_N^-}(m\text{ prime})=(2+o(1))/B,\qquad
 \Pr_{U_N^+}(m\text{ prime})=0.                            \tag{9}
\]

This follows from ordinary PNT and the parity of an actual prime, not from an assumption about prime pairs.

### 3.2 One probability space for all labels and all kernels

Choose a single fair bit `Q in {1,2}`. Conditional on `Q`, independently for **every** pool label `h`, sample an auxiliary integer `Y_h` with law

\[
 Y_h\sim
 \begin{cases}
 U_N^- & h\in T_Q,\\
 U_N^+ & h\notin T_Q.
 \end{cases}
\]

At that label define every kernel from the same integer `Y_h` by (1), and define
`P_h^*=1_P(Y_h)`. This can be done for any finite number of labels, or countably many by a product measure. Restrictions to subsets agree exactly. Prime-factor multisets, multiplicities, all support cutoffs, linear relations between kernels, prime freezing, and all finite Gram/positivity constraints are consequently compatible, not separately postulated.

By (8), conditioning on either value of `Q` changes any permitted local kernel moment by less than any log power. Conditional independence and (9) now give exactly the leading identities (7), uniformly in the choice of pool labels. For a prime anchor, it is its pool that is active; the probability `1/2` of this event cancels the doubled density `2/B`. Kernels elsewhere have the same permitted moments under either parity law. Linear combinations give the identities for arbitrary fixed finite-rank source weights. Repeated labels use the *same* `Y_h` and hence `D_r`, not products of second moments.

This is a projectively consistent realization of the whole leading moment system. Uniformity in label choices permits normalized tuple averages of a fixed family of tests. It does not turn arbitrary growing-degree tests or unbounded signed combinations into controlled tests.

Every inactive pool has **no prime flags on every sample**. For a nonempty set `S` of distinct labels,

\[
 \mathbb E\prod_{h\in S}P_h^*=
 \begin{cases}
 (2^{|S|-1}+o(1))B^{-|S|}, & S\text{ lies in one pool},\\
 0, & S\text{ meets both pools}.
 \end{cases}                                              \tag{10}
\]

For an arbitrary source weight with derivative kernel `F`, freezing the coordinates of `S` yields the more relevant weighted version

\[
 \mathbb E\left[w_H^*\prod_{h\in S}P_h^*\right]
  =(2^{|S|-1}+o(1))B^{-|H|}J_S(F)                          \tag{11}
\]

when `S` lies in one pool, and zero when it meets both. Here
`J_S(F)=integral_(outside S) |integral_S F|^2`, with no factorial inserted. The statement is additive if `J_S=0`. Thus the model satisfies even the hypothetical pure factors `2^(r-1)`, and in particular the weaker published pair upper bound `3.99+O(delta)` on its stipulated good tuples. This does not assert that all of Chen's additional almost-prime distribution statements have been modeled.

Since `M_g/B -> kappa_g`, its prime counts converge in distribution to

\[
 \tfrac12\,\mathcal L(\operatorname{Pois}(2\kappa_1),0)
 +\tfrac12\,\mathcal L(0,\operatorname{Pois}(2\kappa_2)).    \tag{12}
\]

So this obstruction persists for the growing pools, rather than disappearing as an artifact of selecting a fixed tuple.

**Arithmetic limitation.** The `Y_h` are auxiliary integers, not `n+h` for a common `n`. For example they can share a prime `p>z` at labels whose difference is not divisible by `p`. Such an event is exactly impossible for the real translates. The Euler calculation proves that this distinction changes the specified fixed smooth leading moments only by `o(1)` relatively (additively at a zero main term). It does **not** prove closeness in total variation of all divisor observations over `M~B` labels. Any use of those stronger exact observations must retain their real arithmetic law. The theorem established here is non-implication from (7) and its shared-kernel positivity consequences, not non-implication from every known fact about integers.

### 3.3 A strengthened genuine diagonal bound

Take `f(0)=1`, support `[0,a]`, and `4a+2 eta<1`. Under `U_N^-`, the fourth power of its kernel is nonnegative and equals 1 at a prime. By (8)–(9),

\[
 B\,\mathbb E_{U_N}X(f)^4
 =B\,\mathbb E_{U_N^-}X(f)^4+o(1)\ge2+o(1).
\]

Its leading constant is the same `D_4(f,f,f,f)` as the actual common-row fourth moment in (7). Thus

\[
 \mathbb E_R X_h(f)^4=(D_4+o(1))/B,\qquad D_4\ge2.        \tag{13}
\]

For `V_g=sum_(h in T_g) X_h(f)^2`, the uniform two-label identity, the one-label identity, and (13) give

\[
 \operatorname{Var}_R(V_g)\longrightarrow
          \kappa_g D_4\ge2\kappa_g.                       \tag{14}
\]

This uses the elementary mass range, not a growing-order prime theorem. It handles repeated-coordinate terms explicitly and cannot justify replacing sampling without replacement by sampling with replacement. No actual translated Liouville cancellation is being assumed in this deduction: parity cancellation was used only to constrain a local constant through the auxiliary one-dimensional ensemble.

## 4. Why conditioning on all observations is not licensed

The bounded-support tests in (7) form a filtered collection: costs add under multiplication. They are **not an algebra** at a fixed distribution level. Equality against every permitted test therefore cannot be extended to a conditional-expectation identity for the sigma-field they generate. The missing products have moduli beyond that level. Fixed-function asymptotics also do not justify an `N`-dependent approximation to a rare event with error small compared with `B^(-2)`.

A concrete check uses the single-site void

\[
 R_a(m)=1_{P^-(m)>N^a},\qquad 1/3<a<1/2.
\]

Writing `ell_a=log((1-a)/a)`, ordinary PNT and the semiprime integral
`integral_a^(1/2) dt/[t(1-t)]=ell_a` give

\[
 \mathbb E_{U_N^-}R_a=(2+o(1))/B,\qquad
 \mathbb E_{U_N^+}R_a=(2\ell_a+o(1))/B.                   \tag{15}
\]

There are only primes and semiprimes here; square contributions are negligible. For an anchor in the opposite pool the model therefore has

\[
 \mathbb E(P_j^*R_a(Y_h))=(2\ell_a+o(1))/B^2,
\]

not the independence prediction `(1+ell_a+o(1))/B^2`. As `a` tends to `1/2`, the even-sector void disappears. This is consistent with every permitted kernel identity, because the complete void indicator requires uncontrolled inclusion–exclusion products. It illustrates the precise obstruction to “condition on all small-divisor observations and then apply the one-prime theorem.”

At the Gram level the same boundary is visible: an atom of size `2/B` ceases to fit the full derivative-energy form once supports with `a>1/2` and their squares are demanded. The source does not supply those moments. Varying among all fixed subcritical supports cannot be substituted for crossing the boundary.

## 5. Exact finite check

`python3 Submission/check_overlap_consistency.py` passes. It enumerates a **single** 512-row rational probability space with four labels in two pools and three observation bits per label. One shared bit selects even parity in the active pool and odd parity in the other; the all-zero mark is the prime flag. All proper-subset observation moments agree between parity sectors.

The check verifies 2,401 mass moments, 9,604 one-prime moments, 15 prime-pattern identities, 32 shared mixed-kernel Gram entries, and 81 PSD residual checks. All overlapping tests use the same marks. Extending to the complete void observation fails exactly: `0 != 1/64`. This finite analogue checks the consistency mechanism and the failed conditioning step; it does not verify the analytic lemma (8) by experiment and is not a search for prime gaps.

## 6. Remaining arithmetic input and the actual target

For the real CRT rows put `Z_g(n)=sum_(h in T_g) P_h(n)`. The exact missing existence statement is

\[
 \sum_{\substack{N<n\le2N\\n=b\ (W)}}
           1_{Z_1(n)>0}\,1_{Z_2(n)>0}>0                  \tag{16}
\]

at arbitrarily large heights, for every prescribed pair of narrow bands. Stating (16) is a reformulation of the desired occupancy, **not** a new arithmetic estimate.

Two genuinely stronger possible inputs would be:

* a positive lower bound for the actual cross-pool prime-pair sum, possibly with a retained nonnegative common-core divisor weight; or
* a uniform weighted within-pool pair upper factor below 2 in the source normalization, together with the existing occupancy optimization.

Neither is obtained. Nor is the signed averaged AP discrepancy in equation (17) of `AveragedPairWeightAttempt.md` bounded here. No large-sieve/Fourier averaging is repeated. The global parity construction explains why merely extracting further fixed-budget overlap, Gram, or mixed-kernel identities does not remove the missing two-prime information. It does not rule out a new arithmetic estimate using exact divisor-pattern geometry or a genuinely stronger distribution input.

If (16) were proved for the actual primes, the last prime in `T_1` and first in `T_2` would be globally consecutive by the already verified cover, including all unselected pool points. Their global index `j` satisfies `log j/log N -> 1` by PNT. Narrow bands and diagonal selection would then give the requested subsequential limits normalized by `log j`, not by a selected-tuple index. No almost-prime is substituted in this conclusion.

Verification: `Spec.lean` still has its original two `sorry`s and SHA-256
`47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123`.

## 7. Independent verification

The main worker read the full report and cross-checked the displayed BFM divisor identity, CRT counting error, prime-coordinate freezing, and BV error estimate at source lines 1180–1266 and 1354–1504; M18's modified BV and exact pair weight were checked at lines 208–225 and 353–399. The local Euler expansion, parity-neutrality inclusion–exclusion, support margins, prime-atom calculation, and resulting variance identity were independently reconstructed. The auxiliary integers are not common translates; this remains an essential limitation.

The supplied finite checker was rerun and passed all its reported cases; Python byte-compilation passed. An additional independent SymPy/Fraction check verified the Euler coefficient expansion and total pole order for 1 through 7 occurrences, the bilinear Laplace kernel, and the parity-law identities for observation dimensions 2 through 11 and prime-pattern sizes 1 through 12. An initial structural-equality assertion for the symbolic integral was corrected to compare its simplified difference (which is exactly zero); no mathematical formula changed.

Final `lake env lean Submission/Spec.lean` again emitted only the two original `sorry` warnings. Its hash is unchanged. These checks validate the stated obstruction and file status, not either target theorem. No complete argument for (16), and no proof of its failure for the actual primes, has been obtained.
