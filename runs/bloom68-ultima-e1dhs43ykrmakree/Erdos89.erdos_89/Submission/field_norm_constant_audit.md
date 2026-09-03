# Independent audit: field-varying relative norm constants

## Verdict and scope

**No fatal error was found in the fixed-field CM asymptotic or in the CM lower-bound algebra.** The relative norm-element calculation is sound when its analytic sketch is made precise as below. In particular, the factor `2^(1-t)` survives the audit, and the exact integral class/unit obstruction can be removed for a density-one proportion of locally admissible elements. This is not a consequence of the Hasse norm theorem alone.

There are important qualifications and one harmless geometric correction:

* The cited Frobenian/scalar statements do **not themselves state (1)**. Infinite-order log-unit twists require the underlying fixed-character **unitary Hecke** theory, with the radial norm character removed. Merely applying the finite-order Frobenian lemma to these twists would be unjustified. Section 2 supplies the needed formulation and pole check.
* Finite Fourier approximation must be accompanied by truncation of small ideal norms and of ramified valuation vectors. The necessary majorants are available at fixed field; an interchange of infinite limits without them would be a gap.
* If `rho_E` is a covering radius in the maximum-of-complex-moduli norm, the inner difference radius is `2R-2rho_E`, not `2R-rho_E`. The report's `C_E` can be replaced by `2rho_E`, with no effect on the limit.
* For mixed `F`, project into an `E`-embedding **over a real place of F**. A projection over a complex F-place does not identify the relative norm with squared planar distance.

**What is excluded:** the asymptotic CM scheme using the full maximal-order, equal-radius Minkowski polydisks, projecting to the plane, and attempting to make their actual fixed-field limiting distance constants tend to zero by varying the CM extension. The exclusion covers every CM quadratic `E/F`, not just `E=F(i)`.

**What is not proved:** the genuine uniform planar distinct-distance conjecture; a uniform all-sizes estimate for all such polydisks; or a lower bound for actual mixed-signature distance constants. In particular, a lower bound for the mixed **upper capacity** `U` is not a lower bound for the actual distance count. No Lean or Spec changes were made.

## 1. Norm ideals, local norms, and the counting variable

Write `b(a)=1` when every inert prime has even valuation in the nonzero integral F-ideal `a`. With the report's notation,

```
Z(s) = sum_a b(a) (Na)^(-s),
Z(s)^2 = zeta_F(s) L(s,chi) I(s) R(s).
```

The local Euler factors verify this identity directly. At a ramified prime the square of `(1-q^(-s))^(-1)` is supplied by one zeta factor and the extra factor `R(s)`. At an inert prime the extra factor is `(1-q^(-2s))^(-1)`.

Consequently

```
B_id = sqrt(kappa_E/pi) sqrt(I R),
sum_(Na <= Y) b(a) ~ B_id Y/sqrt(log Y).
```

This counts ideals, not norm elements. The appropriate radial variable for the CM element box is **`Y=X^e`**. Replacing `sqrt(log(X^e))` by `sqrt(log X)` without changing the coefficient would introduce an erroneous `sqrt(e)`.

For an integral element `delta`, the integral local conditions are exactly those stated in the report:

* positivity at real places which become complex;
* even valuation at an inert finite prime;
* no restriction at a split finite prime;
* membership in the quadratic local norm group at a ramified finite prime.

At a ramified prime, the restriction of the local quadratic character to units is nontrivial and has conductor `p^(a_p)`. For each fixed nonnegative valuation, exactly half the unit residues modulo that conductor are allowed. This includes wild/dyadic ramification. Local integrality causes no additional restriction: at a nonsplit prime a nonnegative norm valuation forces a nonnegative valuation of the local preimage, and at a split prime an integral product can be represented by `(delta,1)`.

Cyclic Hasse gives an element of **E\*** of exact norm `delta`. It does not by itself give an element of `O_E`. That distinction is resolved in Section 3.

## 2. Ray classes and log units: justification of the local element asymptotic

First take F totally real. Put `f=d_(E/F)`, and let `V` be the totally positive units congruent to 1 modulo `f`. Use the ordinary regulator convention: the determinant after deleting one row of the real logarithm matrix. If `R_F^+` is the corresponding regulator of positive units, the ray exact sequence gives

```
h_f^+ R_V = h_F^+ R_F^+ phi_F(f)
            = kappa_F sqrt(D_F) phi_F(f).                 (A)
```

For clarity, if `m=[O_F^*:O_F^{*,+}]`, then

```
h_F^+ = 2^e h_F/m,
R_F^+ = (m/2) R_F,
kappa_F sqrt(D_F) = 2^(e-1) h_F R_F.
```

Thus (A) has neither a missing sign index nor a missing factor 2. Positive units have no nontrivial torsion here.

### 2.1 The precise character statement needed

Let `S` be the ramified finite primes and `b^S` the indicator on ideals prime to S. Normalize logarithms by

```
ell^0(alpha) = (log tau_j(alpha))_j
                - (log |N_(F/Q) alpha|/e) (1,...,1)
```

for positive `alpha`. These normalized logs lie in the sum-zero hyperplane. The relevant compact ray/log class group is obtained from ideals prime to S and this hyperplane by the relations

```
((alpha), -ell^0(alpha)),  alpha > 0 and alpha = 1 mod f.
```

It is an extension of the finite positive ray class group by the log-unit torus with lattice `ell(V)`. Its characters give unitary Hecke characters `psi` of conductor dividing the positive ray modulus. They include both the finite ray characters and the log-unit modes. The character-twisted ideal series is

```
Z_psi^S(s)
 = [L^S(s,psi) L^S(s,psi chi)]^(1/2)
   product_(p inert) (1-psi(p)^2 q_p^(-2s))^(-1/2).        (B)
```

This Euler identity holds also for the infinite-order unitary characters; it is not restricted to Frobenian twists. The last product converges absolutely for `Re(s)>1/2`.

The fixed-character summatory statement needed is

```
sum_(Na <= Y, (a,S)=1) b(a) psi(a)
 = B^S Y/sqrt(log Y) + o(Y/sqrt(log Y)),  psi=1 or chi;
 = o(Y/sqrt(log Y)),                     otherwise,

B^S = B_id product_(p in S)(1-1/q_p).
```

Here is the important pole check:

1. A unitary Hecke L-function can have a pole on `Re(s)=1` when its character is a pure norm power. Thus the statement “nontrivial character implies no leading pole” is not valid without a normalization.
2. The above normalization removes pure radial norm powers. On every positive rational number `a` that is 1 modulo the finite modulus, `ell^0(a)=0`. A putative character `|N|^(iu)` would therefore have to satisfy `a^(ieu)=1` for all such rationals, forcing `u=0`.
3. Thus the only pole-producing cases in (B) are `psi=1` and `psi=chi`. A nonzero log-unit mode cannot be either one. Equivalently, its nonconstant archimedean log type cannot become trivial after multiplication by the finite/sign character `chi`.
4. In fact `b^S(a) chi(a)=b^S(a)` term by term. The two leading series and their positive leading coefficients are exactly equal, not merely equal in absolute value.

For every other fixed character, the two Hecke L-functions have no pole on that line and admit a fixed-character zero-free region adjoining it. Standard Hecke bounds and the analytic Selberg--Delange argument then give the displayed little-o estimate. Possible exceptional zeros affect a field/character-dependent region, not the leading term. The ideal coefficients have the usual divisor-type bounds, so passing to the scalar series indexed by absolute ideal norms causes no extra hypothesis problem.

The relevant distinction in the citations is this: Frei--Loughran--Newton's displayed Frobenian proposition is finite-order, and Loughran--Matthiesen's displayed lemma is scalar/Frobenian. Their **analytic method**, applied to the explicit factorization (B) and fixed unitary Hecke L-functions, gives the assertion needed here. One should not describe the infinite-order case as a literal application of their Frobenian definition.

Only finitely many characters are needed for each Fourier approximation on the compact group. Uniform estimates over all log-unit modes or over fields are unnecessary. The limiting ideal measure is Haar measure on the kernel of `chi`: relative to normalized Haar measure on the whole compact group its density is `1+chi`. This is the source of the factor 2.

### 2.2 Ramified residue conditions and the factor `2^(1-t)`

Fix the ramified valuation vector and let `s_m=product_(p in S) p^(m_p)`. At each ramified prime choose a local uniformizer to specify the unit part. There are exactly

```
phi_F(f)/2^t
```

allowed unit-residue tuples. For a fixed tuple, weak approximation supplies a positive reference element with those local data. The prime-to-S part of its principal ideal specifies a ray class. Other elements with the same tuple and principal ideal form a coset of V.

For each **allowed** tuple, reciprocity gives `chi=1` on the required prime-to-S ray class. Indeed all the ramified local characters and all the real norm characters are 1, while the remaining local product is precisely that ray character. Hence both leading characters contribute with the same positive sign.

Different tuples can determine the same ray class, but then they determine distinct generator cosets modulo V. Summing over the tuples is therefore not overcounting elements. It correctly retains the unit-residue information.

The resulting multiplier, before the ramified valuation sum, is

```
(phi_F(f)/2^t) * 2/(h_f^+ R_V).
```

If `t=0`, the extension is unramified at finite primes but still nontrivial as a **narrow** class character. The same two leading characters remain, giving 2. The expression `2^(1-t)` is not being interpreted as the reciprocal of an ordinary genus count when `t=0`.

### 2.3 Box volume, and the two truncations

An ideal with generator norm `y` has, averaged over its log-unit torus, exactly

```
(log(Y/y))^(e-1) / ((e-1)! R_V)
```

generators in the positive box. This is the volume of the simplex in the sum-zero log hyperplane, using the coordinate measure obtained by deleting one row. It is an **average**, not a pointwise approximation for each ideal. Most ideals contributing to the main term have `Y/y` of bounded size, so a pointwise large-simplex lattice estimate would not suffice.

Equidistribution from Section 2.1 supplies this average. On `epsilon <= y/Y <= 1`, one can approximate in the radial variable and on the torus by finitely many test functions. The periodicized simplex indicators are bounded there and their boundaries have Haar measure zero. The radial integral is

```
int_0^1 (log(1/u))^(e-1) du = (e-1)!.
```

The missing tails can be controlled without uniform Hecke estimates:

* For any ideal, the number of generators in the box is at most
  `C_F,V (1+log(Y/y))^(e-1)`.
* The untwisted ideal count satisfies
  `sum_(Na<=z) b(a) <<_E,F z/sqrt(log(2z))`.

Partial summation or dyadic decomposition therefore makes the normalized contribution of `y<epsilon Y` tend to zero as `epsilon` tends to zero. For example the relevant majorant is the integrable tail of `(1+log(1/u))^(e-1)` near `u=0`; the range `y<sqrt(Y)` contributes only a lower-order polynomial-logarithmic multiple of `sqrt(Y)`.

The same bounds handle large ramified valuation vectors. Factor out `s_m`, use multiplicativity of b at ramified primes, and first treat `N s_m<=sqrt(Y)`. The main-term tail is bounded by a constant times the tail of the convergent geometric sum `sum_m (N s_m)^(-1)`. For `N s_m>sqrt(Y)`, the number of vectors is only polynomial in `log Y`, and the remaining bound is lower-order. Thus the ramified sum really is

```
sum_m 1/N s_m = product_(p in S)(1-1/q_p)^(-1) = R.
```

Combining this with `B^S`, (A), and the generator average gives the local-norm element asymptotic

```
A_loc(X)
 ~ [2^(1-t)/(kappa_F sqrt(D_F))] B_id X^e/sqrt(log(X^e))
 = [2^(1-t)/sqrt(pi D_F)] [sqrt(kappa_E)/kappa_F]
   sqrt(I R) X^e/sqrt(log(X^e)).                         (C)
```

This establishes the coefficient in (1) for locally admissible elements. The following argument upgrades it to exact integral norm elements.

## 3. Exact integral norms: the switching argument works

Let `I_E` denote fractional ideals and define exactly as in the report

```
H = ker(N:I_E -> I_F) / { (u): u in E^*, N(u)=1 }.
```

Every ideal of norm 1 has zero valuation at nonsplit primes and opposite valuations at the two primes over a split prime. Therefore the map `a -> a/bar(a)` surjects from fractional ideals onto `ker N`.

It factors through `Cl(E)`, since for a principal ideal the quotient has a generator of exact norm 1. Its kernel on `Cl(E)` is the group of **strongly ambiguous** classes:

* An invariant ideal clearly maps to zero.
* Conversely, if `a/bar(a)=(u)` with `N(u)=1`, Hilbert 90 writes `u=v/bar(v)`. Then `a/(v)` is invariant.

In particular,

```
H = Cl(E)/Am_st,
h_T = |H| < infinity.                                  (D)
```

Using ambiguous classes in place of strongly ambiguous classes would lose the unit obstruction. The report correctly uses the latter quotient and exact norm-one generators.

For a locally admissible `delta`, Hasse supplies `z_0` with exact norm `delta`. The valuation conditions supply an integral ideal `J` with `N J=(delta)`. Then `J/(z_0)` lies in `ker N`, and its class in H vanishes exactly when J has a generator of norm `delta`. This proves that H is the obstruction group actually needed, not just a necessary class-group test.

Choose generators `g_1,...,g_k` of H and ideal classes of E mapping to them. Each chosen class is represented by a positive-density reservoir of primes P lying over split F-primes. To see this, use the Hilbert class field of E. It is Galois over F; the Frobenius conjugacy class associated with an ideal class consists of that class and its conjugate. Its restriction to E is trivial, so its underlying F-primes split in E. Chebotarev gives positive density and hence a divergent reciprocal norm sum. Orient each pair `(P,bar P)` to give the desired `g_j`; overlapping reservoirs can be separated into disjoint ones if necessary.

If `p | (delta)` is such a prime, start with the entire p-part of J on `bar P`. Switching one factor to P changes the obstruction by `g_j`, without changing the ideal norm or losing integrality. Having at least `ord(g_j)-1` distinct reservoir divisors for each j permits every needed coefficient modulo `ord(g_j)`. Thus it permits cancellation of **every** obstruction in H.

Here is the density-one step, without an unjustified infinite sieve. For every fixed finite set T of split F-primes, the same local counting proof gives

```
# {delta locally admissible in the box: p | (delta) for all p in T}
 / A_loc(X)  ->  product_(p in T) 1/Np.                  (E)
```

Indeed imposing divisibility multiplies (B) by the finite product `product_(p in T) psi(p)(Np)^(-s)`. At both leading characters `psi(p)=1`, so its main-term value is the stated product. All Fourier and ramification arguments remain unchanged.

For a finite reservoir subset T, let `M_T(delta)` be its number of divisors of `(delta)`. Formula (E), for singleton and pair subsets, gives limiting mean

```
mu_T = sum_(p in T) 1/Np
```

and limiting variance at most `mu_T`. If a fixed number K of switches is required and `mu_T>K`, Chebyshev gives

```
limsup_(X->infinity) Pr(M_T<K) <= mu_T/(mu_T-K)^2.
```

Now enlarge the finite T, **after** taking the fixed-field large-box limit. Divergence of the reciprocal sum makes this tend to zero. A finite union over the generators of H proves that almost every locally admissible element is an exact integral norm.

Therefore `A(X) ~ A_loc(X)`, establishing (1). There is no residual class-number or norm-unit-index factor to insert into its leading constant. No uniform-in-field error is claimed or needed.

## 4. CM distance constant and lower bound

### 4.1 Geometry

In complex-coordinate Minkowski space the maximal-order lattice has covolume `2^(-e) sqrt(D_E)`. Thus

```
n_R ~ (2pi)^e R^(2e)/sqrt(D_E).
```

Projection into one complex embedding is injective. In the CM case the squared planar length of a difference z is the selected real embedding of `delta=N(z)`. That embedding is injective on F, so distinct norm elements give distinct squared distances.

If `rho_E` is a covering radius, round `z/2` to a lattice point x. Both x and `x-z` lie in the radius-R polydisk whenever every `|sigma_j(z)|<=2R-2rho_E`. Consequently, for large R,

```
A((2R-2rho_E)^2) <= D(P_R) <= A(4R^2).
```

This is the corrected form of the report's sandwich. In CM fields every representation of delta has `|sigma_j(z)|^2=tau_j(delta)`, so there is no further balancing issue. Applying (1) proves the actual limit (2), with exactly its stated coefficient.

### 4.2 Class numbers, regulators, and substitution

The ordinary class-number formulas are

```
kappa_F = 2^(e-1) h_F R_F/sqrt(D_F),
kappa_E = (2pi)^e h_E R_E/(w sqrt(D_E)).
```

For CM, `R_E/R_F=2^(e-1)/Q_E`: the embedded F-unit lattice has its real logs multiplied by 2 in the ordinary E-regulator convention, and its index in the E-unit lattice modulo torsion is `Q_E`. Also

```
I_N = [O_F^*:N O_E^*] = 2^e/Q_E.
```

To check the latter, norms of roots of unity are 1 and
`N O_E^*/(O_F^*)^2` has order `Q_E`: a unit whose norm is a square differs from an F-unit by an exact norm-one CM unit, hence by a root of unity.

Biswas's strongly ambiguous formula, with only the infinite places in its S, gives

```
|Am_st| = h_F 2^(t+e-1)/I_N = h_F Q_E 2^(t-1).
```

Together with (D), this yields exactly the Guo--Sheu--Yu/Shyr identity cited by the report:

```
h_E/h_F = Q_E 2^(t-1) h_T.
```

Here t counts finite ramified primes; the e infinite ramification factors have already entered the ambiguous formula. There is no extra `2^e` to add to t.

It follows that

```
L(1,chi) = 2^(t-1) (2pi)^e h_T/(w sqrt(D_E/D_F)).
```

Squaring (2), using `D_E=D_F^2 d`, and substituting this identity gives

```
c(E/F)^2 = [2h_T/(pi w)] (8/pi)^e [sqrt(D_F)/kappa_F] J,
J = I product_(p ramified) q_p^(a_p/2)/(2(1-1/q_p)).       (F)
```

The algebra was checked independently, including a symbolic simplification of the ratio of the two expressions to 1.

### 4.3 Uniform lower bound on these actual limiting constants

Each local factor in J is at least 1. For `q>=4`, use `sqrt(q)>=2`; check `q=2,3` directly. Also `I>=1` and `h_T>=1`.

The Louboutin bound in the cited source is unconditional. Set
`x=log D_F/(2(e-1))>0` for `e>=2`. Then

```
kappa_F <= (exp(1) x)^(e-1) <= exp((e-1)x) = sqrt(D_F),
```

where the second inequality is `1+log x<=x`. For F=Q the same final inequality is equality.

The roots of unity give `phi(w)<=2e`; the elementary estimate `phi(m)>=sqrt(m/2)` gives `w<=8e^2`. Hence

```
c(E/F)^2 >= (8/pi)^e/(4pi e^2) >= 4/pi^3,
c(E/F)   >= 2/pi^(3/2).
```

The minimum of the displayed degree-only square bound occurs at the integer `e=2`: for `e>=2` the ratio of consecutive values is at least `32/(9pi)>1`, and the value at 1 is larger. The lower bound tends to infinity with e.

These inequalities apply to the **actual limiting constants**, not to an upper capacity, because the CM endpoint sandwich proves equality.

## 5. Mixed signature: normalization is correct, but the conclusion is only about U

Take F of signature `(r,s)`, `r>=1`, degree `e=r+2s`, and `E=F(i)`. Then E is totally imaginary with e complex places. At a complex F-place there are two E-places and the relative norm is a product, whereas at a real F-place it is a squared modulus.

### 5.1 The extra archimedean factor

Use weighted ordinary logarithms: `log|tau|` at a real F-place and `2log|tau|` at a complex F-place. There are `r+s` coordinates, their sum is `log |N delta|`, and the box has total radial bound `log Y=e log X`. In the character argument, the mixed normalization is `ell^0(alpha)=ell(alpha)-(log |N alpha|/e)d`, where d has r entries 1 and s entries 2. This again removes radial norm powers. The generator simplex has dimension `r+s-1`; the same factorial cancellation occurs. No angular restriction is imposed at the complex places, so no angular Fourier modes are required for this box.

Since F has a real place, `mu(F)={+1,-1}`, and positive units again have no nontrivial torsion. The mixed version of (A) is

```
h_f^+ R_V = kappa_F sqrt(D_F) phi_F(f)/(2pi)^s.
```

Thus the local and integral norm-element asymptotic gains exactly `(2pi)^s`. The preceding switching proof is still valid. This verifies the norm-capacity calculation leading to (4).

Choose the planar embedding above a real F-place. Every actual difference lies in the radius-2R E-polydisk and its relative norm lies in the stated F-box. The reverse implication is not supplied by the box count: product bounds do not bound each of the two E-coordinates over a complex F-place. Accordingly, the valid conclusion is

```
limsup D(P_R) sqrt(log n_R)/n_R <= U(E/F),
```

not equality with U.

### 5.2 Exact relative units and the factor `I_N/2`

The relative unit rank is

```
(e-1) - (r+s-1) = s.
```

Akhtari--Vaaler's relative units are defined modulo torsion, with norm torsion in F. Here a torsion norm must be **+1**, because it is positive at every real F-place. Thus their group is precisely the report's group of exact relative units modulo roots of unity. All roots of unity of E also have norm 1.

Their determinant deletes one E-place above each F-place. Above a real F-place there is only one E-place, leaving no relative row. Above each complex F-place one row remains, with entry `2log|sigma(u)|`. This is exactly the report's `R_rel`; it is not an unweighted logarithmic determinant and not an Euclidean hyperplane covolume.

Writing `F_F=O_F^*/mu(F)` and `I_free` for the norm image in this torsion-free group, their regulator identity is

```
R_E/R_F = [F_F:I_free] R_rel.
```

Because `-1` is not a norm and `mu(F)={+1,-1}`,

```
[F_F:I_free] = [O_F^*:mu(F) N O_E^*] = I_N/2.
```

Therefore the report's normalization

```
R_E/R_F = (I_N/2) R_rel
```

is correct. Dropping this division by 2, or replacing each `2log` by `log` without changing the formula, would be incorrect.

Combining it with

```
|Am_st| = h_F 2^(t+r-1)/I_N,
h_E/|Am_st| = h_T
```

and the two ordinary class-number formulas gives

```
L(1,chi) = 2^(t-1) (2pi)^(e-s) h_T R_rel
           /(w sqrt(D_E/D_F)).
```

Substitution in (4) gives precisely

```
U(E/F)^2 = [2h_T R_rel/(pi w)] (8/pi)^e (2pi)^s
            [sqrt(D_F)/kappa_F] J.                       (G)
```

This algebra was also checked independently by symbolic simplification.

### 5.3 What the height bounds do and do not imply

The 2015 Akhtari--Vaaler bound alone is an **upper bound for a regulator in terms of a chosen height product**; it cannot be reversed. The needed reverse-direction existence result is in their 2020 paper: there exist independent relative units with height product at most `s! R_rel`. With the cited Voutier estimate it does yield

```
R_rel >= V(2e)^s/s!,
V(d) = (1/4)(loglog d/log d)^3,
```

for the mixed case `s>=1` (hence `2e>=6`). For `s=0`, use the empty determinant `R_rel=1` separately.

Thus `U->0` in degree-growing families requires

```
R_rel = o(e^2 (pi/8)^e (2pi)^(-s)).
```

The stated height bound prevents this for bounded s, and more generally for `s log e=o(e)`. It does not settle proportional mixed rank. The quoted Friedman--Skoruppa constants are indeed too weak to remedy this merely by invoking an unspecified exponential lower bound.

**Logical boundary:** these are restrictions on making the explicit upper bound U tend to zero. They do not exclude actual mixed distance constants tending to zero, even in the low-mixed-rank regimes. An actual distance constant can be much smaller than its positive upper capacity. The report appropriately labels (4) an upper bound; any stronger family exclusion inferred from (G) would be a fatal inference error.

## 6. Source checks and independent calibrations

The following local corpus passages were inspected, not just their bibliographic descriptions:

* `/corpus/src/1810.06024/1810.06024.tex`, lines 311–413: number-field Frobenian definition, Euler factorization, and fixed-character analytic argument. This is not by itself the infinite-order log-unit equidistribution theorem.
* `/corpus/src/1904.12845/1904.12845.tex`, lines 532–604: scalar analytic factorization and Selberg--Delange summation.
* `/corpus/src/1411.7775/1411.7775.tex`, lines 18–35: cyclic Hasse norm theorem, for field elements rather than integral elements.
* `/corpus/src/1905.11649/classnoCMtoriNMJ.tex`, lines 95–102 and 792–797: Hasse unit index and the CM norm-one torus class-number identity.
* `/corpus/src/1610.00733/1610.00733.tex`, lines 265–315: strong versus ordinary ambiguity, the unit-norm quotient between them, and the strongly ambiguous class-number formula.
* `/corpus/src/2007.10313/UEMTNF.tex`, lines 133–138: the unconditional Louboutin residue upper bound.
* `/corpus/src/1508.01969/1508.01969.tex`, lines 318–409: norm modulo torsion, the relative determinant convention, and the regulator ratio.
* `/corpus/src/2008.06124/2008.06124.tex`, lines 255–273, 845–864, and 1429–1432: existence of small height products, the explicit Voutier bound, and the regulator identity.
* `/corpus/src/1003.1094/1003.1094.tex`, lines 77–86 and 138–157: Bernays's fundamental-discriminant constant and the distinction between genus representation and representation by a class.
* `/corpus/src/1406.0120/1406.0120.tex`, lines 249–250: the actual Friedman--Skoruppa constants and exponents.

Checks beyond formal substitution:

1. **All imaginary quadratic fields over Q.** Formula (1) reduces to
   `2^(1-omega(D_E)) sqrt((|D_E|/phi(|D_E|)) L(1,chi) I/pi)`, exactly the cited Bernays formula for a fundamental discriminant. In particular Q(i) gives the Landau--Ramanujan coefficient and `c^2=8I/pi^2`.
2. **A finite-unramified CM example.** For `E=Q(zeta_12)`, `F=Q(sqrt(3))`, one has `D_F=12`, `D_E=144`, `t=0`, `h_F=h_E=1`, `R_E=R_F=log(2+sqrt(3))`, `Q_E=2`, and `h_T=1`. Thus the apparently unusual factor 2 is compatible with the class/regulator identities. Direct enumeration in `Z[zeta_12]` gave `A(500)=24497`, `A(1000)=92035`, `A(2000)=348205`. The normalized coefficients `A(X)sqrt(log(X^2))/X^2` were respectively `0.345458`, `0.342087`, `0.339408`, approaching the predicted coefficient approximately `0.318984`. This is only a finite-size sanity check, not an analytic proof. The enumeration used the exact norm formula
   `N(a+b*zeta+c*zeta^2+d*zeta^3)=(a^2+ac+c^2+b^2+bd+d^2)+(ab+bc+cd)sqrt(3)`.
3. **Mixed regulator normalization.** PARI, with `bnfcertify` successful for both fields, was used for `F=Q(theta)`, `theta^3-theta-1=0`, and `E=F(i)`. Here F has signature `(1,1)`. Norms of an E fundamental-unit basis have exponents `[2,1]` in the F free unit group, so the free norm index is 1 and `I_N=2`. An exact norm-one generator has weighted archimedean logs `(a,0,-a)` with `a=3.642542601025807...`. Directly `R_E/R_F=3.642542601025807...`, confirming `(I_N/2)R_rel`, not `I_N R_rel`.

## 7. Final interpretation for the conjecture

The fixed-field-then-large-size diagonal logic in the research report is legitimate. If actual constants tended to zero, one could fix each field first and then take R arbitrarily large; a field-dependent starting threshold would not obstruct a disproof. The CM calculation blocks that scheme because its **actual** constants are bounded below, not because of any threshold issue.

Conversely, fixed-field positive limits alone do not give one lower bound valid at all sizes simultaneously across varying fields. Nor does this audit cover subsets of these polydisks, other shapes/orders, or arbitrary planar point configurations. For mixed F, the actual distance asymptotic remains unestablished by this norm-capacity calculation, and lower bounds for U cannot substitute for it.

**Bottom line:** with the explicit fixed-field Hecke and saturation justifications above, the CM constant obstruction is valid for the specified asymptotic family. The mixed regulator algebra is correctly normalized, but it describes an upper capacity only. Neither a proof nor a disproof of the genuine uniform planar distinct-distance conjecture follows.
