# Global missing-band Selberg-form model

## Status and scope

**This is an exact positive-form construction, not a prime theorem or an integer realization.** It answers the global-consistency question affirmatively on the ordinary unconditional Selberg simplex, and on every support enlargement lying in the coordinate cap specified below. It gives all exact binary-pattern forms at once, for every finite offset set and every complex, possibly entangled test function.

There are two necessary qualifications:

1. An unspecified "pure r-point upper form" is not automatically satisfied. The exact r-point form of the model is computed below, giving an explicit comparison criterion for every proposed upper bound.
2. An enlarged-support theorem using truncated one-prime integrals is not an assertion of the same full one-prime operator on a larger simplex. Such a theorem must be compared with its actual functionals. The construction below does not settle every possible enlarged-support system.

`Submission/Spec.lean` was not modified. Its SHA-256 is

```
47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123
```

No Lean proof or admission is used in this argument.

## 1. Exact theorem

Fix `0 < a < b < 2a`, and put

```
T = a+b,    p = a/T,    c = 1/p = T/a.
```

Thus `1/3 < p < 1/2` and `2 < c < 3`.

Choose a fixed ambient coordinate length `R <= p`. For a finite set A of distinct real offsets, use

```
H_A = tensor_(x in A) L²(0,R).
P = |1><1|,       (Pf)(t) = integral_0^R f(s) ds,
P_S = tensor product of P on S and identity on A\S.
```

Here `||P|| = R`. In particular, `0 <= cP <= I`.

For a common phase `u`, uniform modulo T, define the independent stripe set

```
Sigma_u = union_(n in Z) [u+nT, u+nT+a).
```

Any two points in one interval have separation less than a; points in different intervals have separation greater than b. Hence Sigma_u contains no pair at distance in `(a,b)`.

Define the local prime effect

```
q_x(u) = 1_(x in Sigma_u) cP.
```

For an EXACT prime pattern D subset A, define

```
M_A(D) = (1/T) integral_0^T
         [tensor_(x in D) q_x(u)]
         [tensor_(x in A\D) (I-q_x(u))] du.                 (1)
```

The brackets specify different tensor factors, not an uncompressed product on a simplex.

Every integrand is positive. Moreover

```
M_A(D) >= 0,        sum_(D subset A) M_A(D) = I.
```

Thus (1) is a positive operator-valued probability measure (POVM). A pattern containing a forbidden edge has zero effect.

For S subset A put

```
sigma(S) = (1/T) measure{u : S subset Sigma_u},
gamma(S) = c^|S| sigma(S),
gamma(empty) = 1.
```

Summing (1) over all D containing S gives the exact all-prime moment

```
sum_(D contains S) M_A(D) = gamma(S) P_S.                 (2)
```

In particular,

```
gamma({x}) = 1;
gamma({x,y}) = 0 if |x-y| in (a,b);
0 <= gamma(S) <= c^(|S|-1) for nonempty S.                (3)
```

The exact-pattern formula can equivalently be written

```
M_A(D) = sum_(U subset A\D) (-1)^|U| gamma(D union U) P_(D union U).
```

Its positivity is proved by (1), not assumed from its alternating expansion.

## 2. Actual simplex-supported and entangled functions

Use physical logarithmic coordinates, so that the ordinary unconditional support is

```
Delta_A(rho) = {t_x >= 0 : sum_(x in A) t_x <= rho},
```

with `rho` close to `1/4`. Suppose `rho <= R`, and let C_A be the zero-extension projection from H_A onto `L²(Delta_A(rho))`.

Define the physical exact-pattern effects by

```
E_A(D) = C_A M_A(D) C_A, restricted to range(C_A).         (4)
```

They are positive and sum to the identity of the physical space. For any nonzero complex F in that space,

```
Pr_F(exactly D prime) = <F,E_A(D)F> / ||F||²
```

is a probability distribution, supported on independent sets of the band graph.

Write

```
J_S(F) = integral_(t_(A\S)) | integral_(t_S) F(t) dt_S |² dt_(A\S),
I(F) = ||F||²,
```

where F is zero-extended. Equation (2) gives, simultaneously for all F,

```
Pr_F(all S prime) = gamma(S) J_S(F) / I(F).               (5)
```

Thus the one-prime form is exactly J_i, the forbidden-pair forms vanish, and all higher forms are explicit.

**Important:** `C_A P_S C_A` is generally NOT the product of the individually compressed operators `C_A P_i C_A`. The latter need not commute. The construction uses a joint measurement before compression and compresses its whole family. No tensor factorization of F or of the simplex is assumed.

For every band in the question, the SAME ambient coordinate space `L²(0,1/3)` works. Consequently it covers the ordinary `rho ~ 1/4` simplex and any support whatsoever contained in `[0,1/3]^A`, even if its total support is larger. For a fixed band one can instead use `R=p` and cover every support contained in `[0,p]^A`.

## 3. Projective consistency, including the support issue

The phase in (1) is one global phase, not a phase chosen separately for each tuple. For A subset B the uncompressed effects satisfy the literal operator identity

```
sum_(D subset B, D intersect A = D0) M_B(D)
    = M_A(D0) tensor I_(B\A).                            (6)
```

This includes arbitrary entangled test states on B.

The physical simplexes do NOT tensor-factor. Nevertheless `C_B <= C_A tensor I`, and hence after compression (6) becomes

```
sum_(D intersect A = D0) E_B(D)
    = C_B (E_A(D0) tensor I) C_B,                         (7)
```

where E_A is extended by zero to H_A.

For a density matrix tau_B supported on the B-simplex, let

```
tau_A = partial_trace_(B\A)(tau_B).
```

Then tau_A is supported on the A-simplex, and (7) implies

```
sum_(D intersect A = D0) Tr(tau_B E_B(D))
    = Tr(tau_A E_A(D0)).                                 (8)
```

Partial traces compose, so this is genuinely projective consistency.

For a pure entangled F_B, tau_A is usually mixed. It is incorrect to demand that forgetting coordinates always produce another pure test function, or to use `|integral F_B dt_(B\A)><integral F_B dt_(B\A)|` as its partial trace. The all-F quadratic forms extend linearly to mixed states and give precisely (8).

Support changes are also compatible: zero extension from a smaller support to a larger one commutes with restriction of the fixed ambient forms. For general dimension-dependent support domains, the corresponding support inclusion under coordinate projection must be checked; the ordinary fixed-radius simplex has it.

### A literal common ambient Hilbert space

The finite tensor spaces form a single quasi-local operator algebra, with the inclusions in (6). For a Hilbert-space realization, choose any unit reference vector in `L²(0,R)` and take the incomplete infinite tensor product indexed by all real offsets. Every finite tensor algebra acts on this one, generally nonseparable Hilbert space.

There is also a common commuting-projection dilation. Write `Pi=P/R`, add one uniform ancillary variable `v_x in [0,1]` at each site, and add the common phase. On the resulting tensor/direct-integral Hilbert space put

```
Q_x = 1_(x in Sigma_u) Pi_x 1_(v_x <= cR).
```

The Q_x are commuting projections. Compression to constant ancillary vectors and constant phase gives (1). Thus all the binary event identities can hold on one ambient space; the model is not just a list of separate scalar witnesses.

Different test functions are different states/weights on this measurement. Projective consistency does not mean that independently choosing unrelated F_A and F_B must give identical scalar marginals.

## 4. Translations and continuous parameters

Translation of all offsets changes u by the same translation, so every sigma(S), gamma(S), and finite effect is translation invariant after canonical coordinate relabeling. The common Hilbert realization has the corresponding unitary covariance by site permutations and phase shifts.

For a fixed ordered tuple of distinct sites, identify its test spaces in the usual way. Moving one site by h changes its phase arc in measure at most `2|h|`. Consequently

```
|sigma(S;x)-sigma(S;x')| <= (2/T) sum_(i in S) |x_i-x'_i|.
```

The exact-pattern operators are likewise operator-norm continuous under this finite-tuple identification. They are continuous in `(a,b)` locally, by writing `u=T v`, `v in [0,1)`, and using a fixed safe R. The ambient `R=1/3` works throughout `0<a<b<2a`.

This is finite-configuration continuity, not a claim that site permutation on an uncountable tensor product is a strongly continuous representation of R. It generally is not. Nor is collision of two distinct tensor coordinates an identification with a single coordinate. Physically repeated offsets are identified as one site from the outset. Distinct microscopic offsets having the same normalized limiting position can instead be kept as distinct labels with a common position parameter; formulas (1)-(5) extend to that situation without change.

A demand for a strongly continuous action translating the full independent one-site operator algebras would be an additional, incompatible requirement on this tensor-local interpretation: for local operators A_x and B_x, the translate A_(x+h) commutes with B_x for every nonzero h. Strong continuity at h=0 would force A_x to commute with B_x, contrary to a noncommutative one-site algebra. This issue is present even without a missing band. It does not affect the finite-configuration norm continuity just proved.

## 5. Pair and all higher pure upper bounds

The model passes every scalar pure upper bound

```
prime(S) <= C_S J_S
```

for which `C_S >= gamma(S)`. In particular,

```
prime(i,j) <= c J_ij < 3 J_ij < 3.99 J_ij,
prime(S) <= c^(r-1) J_S < 3^(r-1) J_S,   r=|S|>=2.        (9)
```

All these inequalities hold as operator inequalities and simultaneously for every entangled F. Any hierarchy `C_r >= 3^(r-1)` is therefore sufficient for all r; larger sieve constants do not cause a problem.

The sharp uniform constant for THIS construction is `c^(r-1)`. Indeed, put r distinct offsets in an interval of diameter d<a. Then

```
sigma(S) = (a-d)/T,
gamma(S) = c^(r-1) (1-d/a),
```

which tends to `c^(r-1)` as d tends to zero. There are simplex-supported F with `J_S(F)>0`.

For a non-scalar pure upper form U_S, the exact condition is the quadratic-form domination

```
U_S(F) >= gamma(S) J_S(F)
```

on its stated domain. One cannot honestly claim that the construction satisfies "any" unspecified, arbitrarily stronger upper form. A proposed higher-point improvement must be compared with (5), including its actual domain and normalization.

All deterministic independent-set constraints, including weighted prime-count bounds, odd-cycle inequalities, and higher-degree inequalities nonnegative on independent patterns, hold automatically because every exact-pattern effect in (4) is positive and forbidden patterns have zero effect.

## 6. What the simplex does and does not repair

### Full tensor support at coordinate length 1/2 is genuinely impossible

Let the band graph contain a cycle on `2m+1` vertices. For an independent binary pattern, at most m of these vertices are prime. Hence any positive joint family with zero edge pairs satisfies

```
sum_i prime_effect_i <= m I.
```

On the full tensor product of `L²(0,1/2)`, the unit constant tensor vector has one-prime expectation `1/2` at every site, yielding total expectation `m+1/2`, a contradiction.

Such cycles exist for every b>a: choose m with `(m+1)/m < b/a`, choose `a/m < u < b/(m+1)`, walk m forward steps of length `(m+1)u` followed by m+1 backward steps of length `mu`. The intermediate vertices are distinct and form an odd cycle. Additional chords do not affect the contradiction.

This test vector is not in the physical fixed-total-support simplex. Thus it does not contradict Sections 1-3.

### Sharp threshold for the exact stripe moments on a full simplex

The condition `rho <= p=1/c` is not merely an artifact of checking the local conditional effects. It is NECESSARY for the exact moments (5) to define positive binary patterns on every full simplex of radius rho.

Suppose `rho>1/c`. Choose two distinct offsets with separation d>0 so small that

```
alpha = gamma({i,j}) = c(1-d/a),       alpha rho > 1.
```

Choose `1/alpha < L < rho` and `0<epsilon<rho-L`. The rectangle-supported test

```
F(t_i,t_j) = 1_(0,epsilon)(t_i) 1_(0,L)(t_j)
```

lies in the rho-simplex, but

```
J_i(F) - alpha J_ij(F)
  = epsilon² L (1-alpha L) < 0.                         (10)
```

This would be the mass of the event "i prime and j nonprime". It cannot be negative. Smooth tests can replace the indicator functions by approximation, since the inequality is strict and the forms are bounded.

Thus the fixed-total-support constraint does not extend THESE exact stripe moments past the cap p. This is not a theorem excluding every other choice of higher moments or every differently constrained support.

A rational example is

```
a=1, b=3/2, c=5/2, p=2/5,
rho=9/20, d=1/100, epsilon=1/50, L=21/50.
```

The support has total width `11/25 < 9/20`, and (10) is exactly

```
-1659/250000000.
```

## 7. Enlarged-support arithmetic must use the correct form

The standard full-simplex construction covers `rho~1/4` with room to spare. It also covers every enlargement whose coordinate cap is at most p, whether or not its total support is at most p.

For the epsilon-enlarged simplex in Polymath's *Variants of the Selberg sieve*, the unconditional/BV normalization has

```
R_epsilon = (1+epsilon)/4,
s_epsilon = (1-epsilon)/4,
```

and uses the truncated one-prime input

```
J_i,tr(F) = integral_(sum_(j!=i) t_j <= s_epsilon)
             | integral F dt_i |² dt_(j!=i).
```

This is a lower-bound input, NOT an assertion that the full J_i is an asymptotic throughout the larger simplex. The source explicitly explains this distinction.

Whenever `R_epsilon<=p`, our stronger full-J_i model is compatible with that lower input too, subject to comparing any additional upper forms as in Section 5. Uniformly for all bands in this question, `epsilon<=1/3` is covered; this includes the unconditional `epsilon=1/25` example in the source.

For larger epsilon, (10) rules out retaining the same exact stripe moments AND the full J_i. It does not rule out a completion using the actual truncated inputs or different moments. No universal claim about all enlarged-support variants is made here.

**Concrete next mathematical target:** fix a band and an epsilon with `R_epsilon>p`. Prove an extension-or-separation theorem for positive exact-pattern forms on `L²(Delta_A(R_epsilon))` which vanish on forbidden patterns, have normalization I, reproduce the full one-prime forms on the ordinary subdomain, dominate the explicitly displayed truncated inputs on the larger domain, and satisfy the actually available higher upper forms on their stated domains. An extension must include compatible embeddings/restrictions, not independently chosen tuple witnesses; a separation must give a finite tuple and a certified quadratic-form inequality. In setting up this target, do not add an unproved full one-prime identity or a new tensor-marginality assertion merely because it would simplify the problem.

There is no opening within just the ordinary full-J_i support system and the upper hierarchy in (9): the construction is a countermodel to that proposed inference. Enlarged-support data or genuinely arithmetic mixed information would have to do new work.

## 8. Arithmetic data not modeled

The construction does NOT provide:

- An integer set, prime sequence, or actual indicators `1_P(n+h)` with these weighted laws.
- Bombieri-Vinogradov estimates, their uniformity/error terms, or a realization of divisor coefficients by integers.
- CRT-row and roughness compatibility, local singular-series factors, or the exceptional-modulus requirements of the cited sieve theorems.
- Mixed arithmetic identities between different sieve-weight representations, moduli, heights, or translated rows beyond the explicitly proved abstract operator covariance and marginal identities.
- Complete factor-pattern measures, the cofactor constraints discussed in `JointExactPatternAudit.md`, or their joint compatibility with this model. Separate countermodels cannot simply be combined.
- A proof concerning globally consecutive actual primes or Erdős #5.

It models exactly the stated positive-form data and the indicated pure upper inequalities. It is an information-obstruction certificate, not a claim that primes can actually have the missing band.

## 9. Verification and source checks

The operator identities above are exact proofs. An independent finite-dimensional check used `a=1`, `b=3/2`, and the induced 7-cycle at offsets

```
0, 7/5, 14/5, 21/5, 63/20, 21/10, 21/20.
```

The stripe law was computed with rational phase endpoints (14 phase patterns). A 36-dimensional orthonormal box-function space was chosen wholly inside the actual `rho=1/4` simplex. All 128 exact binary effects were tested: normalization, all-order moment identities, forbidden-pair zeros, and positivity. The smallest computed eigenvalue was `-4.02e-17` (roundoff); the maximum moment-identity error was below `7e-18`. An arbitrary complex entangled state gave total probability `1+2.3e-16`. A separate product-space calculation verified the tensor marginal identities. The negative example in Section 6 was checked with exact rational arithmetic.

Sources inspected:

- `Submission/JointExactPatternAudit.md`, especially Section 5 and the conclusion, for the distinction between form countermodels and arithmetic factor-pattern realizations.
- `/corpus/src/1811.03008/limitp2.tex`, lines 350-390: the actual 3.99 prime-pair upper form and its small-support/CRT hypotheses.
- `/corpus/src/1407.4897/newergap-submitted.tex`, lines 553-568: the standard I and J_i functionals; lines 625-666: the enlarged and vanishing-marginal variants; the proof beginning at line 1333 explicitly distinguishes a truncated lower bound from a full prime asymptotic.

## 10. Independent source/normalization audit and consecutivity caveat

A second research agent checked the actual all-order sieve input; the main
assistant independently read the cited passages and checked the auxiliary
integral. Neither BFM nor Merikoski states a Chen-improved hierarchy with
constants `2^(r-1)`. A directly justified Selberg/BV family, for tiny original
total support delta and each fixed r, has multiplier

```
C_r(delta) = min((r-1)!/(1/4-2delta)^(r-1),
                 r!/(1/2-2delta)^r).
```

The first expression keeps one prime exact and majorizes the other r-1;
the second sieves all r using the nonprime CRT expansion. The optimal
m-dimensional auxiliary cost is `m!/sigma^m`: Cauchy--Schwarz against a
simplex of volume `sigma^m/m!` gives the lower bound, approached by
`G(t)=(1-sum(t)/sigma)_+^m`. The leading constants at r=2,3,4,5 are
4,32,384,3840, with the pair entry improved separately to 3.99 by Merikoski.
No growing-r uniformity is claimed. These constants exceed the stripe
model's `c^(r-1)`, so they do not invalidate its all-order completion.

Relevant checked sources: BFM1404.5094, 1280--1351 and 1506--1626;
nonprime error budget 1354--1389; Polymath1407.4897, 496--541;
Merikoski1811.03008, 353--390 and 656--675. In the last source the Chen
coefficient is Omega1-Omega2+Omega3, bounded by
`4.19-0.279+0.076=3.987`, not an iteratable factor 2.

There is also a concrete common scalar-field realization of the ordinary
forms, including their polarization across different test functions. On
`L²(0,ell)`, ell=1/4, choose e0=ell^(-1/2) and an orthonormal completion in
which every coefficient c_nu of `g_B=sqrt(B)1_(0,1/B)` is nonzero (B>4).
Choose independent nu_x with probabilities c_nu^2, independent uniforms
xi_x, and the one common stripe phase. Define

```
Z_x=1_(x active) 1_(nu_x=0) 1_(xi_x<=ell/p),
D_F=(-1)^K B^(-K/2) Fhat(nu_x1,...,nu_xK)/product c_nu_xi.
```

These use one binary field and one linear map in F, not separately chosen
laws for each F. Parseval gives

```
E|D_F|²=B^(-K) I(F),
E[|D_F|² product_(i in S) Z_i]
  =B^(-K) sigma(S)/p^|S| J_S(F).
```

For a local smooth primitive test phi supported below ell, the random
linear functional

```
L_phi(x)=-<phi',e_nu_x>/(sqrt(B)c_nu_x)
```

obeys `Z_x=1 => L_phi(x)=phi(0)`,
`E L_phi L_psi=B^(-1)<phi',psi'>`, and
`E L_phi=phi(0)-phi(1/B)`. Products of these same local functions give the
multicoordinate weights. This strengthens the overlap check within the
listed ordinary forms. It still does not realize integer divisor patterns,
CRT arithmetic, or all mixed factor statistics.

Finally, a missing band of CONSECUTIVE gaps does not generally imply that
all occupied survivor positions form a pair-distance independent set. For
`a/2<d<b/2` and `b<2a`, the occupied positions 0,d,2d have both consecutive
gaps below a, but an endpoint distance in (a,b). The genuine forbidden cell
for ordered survivors i<j is

```
P_i P_j product_(i<k<j)(1-P_k)=0.
```

The model in this report satisfies the STRONGER pairwise prohibition, so
this correction does not rescue a deduction from the modeled data.
Conversely, a hypothetical contradiction obtained only from pairwise
independence would still need a legitimate consecutivity argument before
it could prove Erdős #5.

