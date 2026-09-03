# Characteristic-two trace selectors in nonscalar cubic Bose quotients

## Result and scope

The proposed index-13 half-trace construction does **not** give an infinite family of cyclic strong B3 sets. There is no exceptional Artin–Schreier relation protecting its six selected roots. In fact, there is a deletion-robust obstruction:

> Let `q` be a power of two, `K/F_q` have degree three, `theta` have degree three, and let `H <= K*` have fixed order `h` and contain a nonscalar element. For
>
>     S = {t in F_q : Tr_(q/2)(L t) = c},   L != 0,
>
> every cyclic strong B3 subset `A` of `{(theta+t)H : t in S}` satisfies, uniformly in `theta,L,c,H`,
>
>     |A| <= 5q/12 + O_h(sqrt(q)).                         (1)

In particular, for `q=2^(4m)`, `gcd(m,3)=1`, and `h=13`,

    limsup |A|^3 / ((q^3-1)/13) <= 1625/1728 < 1.          (2)

This includes arbitrary pruning of the half-trace selector, not just the full selector. No primitivity assumption on theta is used. Thus theta in `F_4096 \ F_16`, as well as arbitrary degree-three theta over F_q, is covered.

There is also a bounded-rank trace-cell version. If independent binary linear forms

    ell_j(t) = Tr_(q/2)(L_j t),   1 <= j <= r,

are used, `r` is fixed, and `S` is any nonempty union of their cells, put

    rho = |S|/q = |C|/2^r,  C subset F_2^r.

Then

    |A| <= (5 rho/6) q + O_(r,h)(sqrt(q)).                 (3)

Every such full selector has a nontrivial quotient collision for all sufficiently large q, uniformly in all its parameters. For index seven, density `rho=5/8` gives the particularly useful bound

    limsup |A|^3 / ((q^3-1)/7)
        <= 7(25/48)^3 = 109375/110592 < 1.                (4)

For example, along the same `q=16^m`, `3` not dividing `m`, use any ten cells of the fixed-field map `Tr_(q/16)(L t)`: this has density 5/8, and order-seven H is nonscalar. A rank-three binary trace map and five of its eight cells is another implementation; it does not require F_8 to be a subfield of F_q.

These statements concern **cyclic** strong B3 in `K*/H`, equivalently modular triple sums. They do not assert that every integer lift of a modular collision is an integer collision. They close this proposed cyclic certificate for a disproof, not the unchanged open integer asymptotic in `Spec.lean`. No resolution of that specification is claimed.

The proof is algebraic plus standard bounded-degree Lang–Weil and geometric-integrality specialization. The accompanying Sage audit is exact, but is only a diagnostic, not the asymptotic proof.

## 1. Exact collision equation and the two matrix facts

Write

    f(X) = X^3 + f_2 X^2 + f_1 X + f_0

for theta's monic irreducible polynomial, and identify `K` with `F_q[X]/(f)`. For a fixed `zeta in H \ F_q*`, let `M_zeta` be multiplication by zeta on polynomials of degree at most two, reduced modulo f. For monic cubics P,Q, the exact equivalence is

    P(theta) = zeta Q(theta)
    iff
    P = f + M_zeta(Q-f).                                 (5)

Indeed P-f and Q-f have degree at most two, and evaluation at theta is injective on that three-dimensional space. In characteristic two the minus signs may of course be written as plus signs.

Use independent coefficient variables

    Q = X^3 + a X^2 + b X + c,
    P = X^3 + A X^2 + B X + C,

where `(A,B,C)` is the invertible affine transform specified by (5). Two consequences of nonscalarity will be used repeatedly.

**Matrix fact I.** The linear part of A is not proportional to a.

Let `ell_2` extract the X-squared coefficient. If `ell_2 M_zeta` were proportional to `ell_2`, its values on 1 and X would vanish. Write `zeta=z_0+z_1 theta+z_2 theta^2`. The first vanishing gives `z_2=0`, and the second then gives `z_1=0`, contradicting nonscalarity.

**Matrix fact II.** The two irreducible affine quadrics

    d_Q = ab+c,                 d_P = AB+C                (6)

are different divisors in coefficient space.

The second is an invertible affine pullback of the first, so it is irreducible of degree two. If `d_P=kappa d_Q`, their homogeneous quadratic parts give

    A_lin B_lin = kappa ab.

Unique factorization forces both A_lin and B_lin to have zero c coefficient. These coefficients are the X-squared and X coefficients of `M_zeta(1)=zeta`. Hence zeta would be scalar, a contradiction.

Both facts hold after extending constants to an algebraic closure. They require no special choice of f or of theta.

## 2. The characteristic-two sign field: the double pole really matters

Work geometrically over `k=overline(F_q)`. A generic monic cubic has Galois group S3: the field of its three independent ordered roots has invariant field given by the elementary symmetric functions. The unique quadratic subfield is its Artin–Schreier sign field.

For `R=X^3+aX^2+bX+c`, its sign class is

    B(R) = (a^3 c + abc + b^3 + c^2)/(ab+c)^2.            (7)

For verification, with roots x,y,z, take

    eta = x/(x+y) + x/(x+z) + y/(y+z).

An odd permutation adds 1 to eta; an even permutation fixes it. Moreover

    eta^2+eta = sum_{i<j} r_i r_j/(r_i+r_j)^2 = B(R).

Here `(x+y)(x+z)(y+z)=ab+c`. The numerator identity is also checked symbolically in the audit.

Set `d=ab+c`. Formula (7) becomes

    B(R) = 1 + a(a^2+b)/d + b(a^2+b)^2/d^2.              (8)

At the generic point of `d=0`, the residue field is `k(a,b)`. Its leading double-pole coefficient

    b(a^2+b)^2

is **not a square** in that residue field, because b is not a square. If `g^2+g` has a pole of order two at this valuation, g has a simple pole, and the leading coefficient of `g^2+g` is a square. Thus (8) cannot be made regular by adding an Artin–Schreier coboundary.

This is the needed treatment of the characteristic-two subtlety. A double pole cannot simply be declared removable: the residue field at a divisor is imperfect even though k is algebraically closed. Here its nonsquare leading coefficient proves the opposite.

By Matrix fact II, `B(P)` is regular at the generic divisor `d_Q=0`. Consequently `B(Q)+B(P)` has the same nonremovable double pole as (8). The two sign fields are distinct, even geometrically. Any nontrivial common Galois quotient of two S3 extensions has a quadratic quotient. It follows that their splitting fields are linearly disjoint, with compositum

    E / k(a,b,c),          Gal(E/k(a,b,c)) = S3 x S3.     (9)

Equivalently, the variety of the two ordered triples of distinct roots satisfying (5), with `d_P d_Q != 0`, is geometrically integral of dimension three. Call it X.

## 3. At infinity all trace combinations have a simple pole

Compactify the coefficient space to projective three-space. At the generic hyperplane at infinity use

    a=1/s,    b=u/s,    c=v/s.

The Q roots consist of one root

    s^(-1) + O(1)

and two finite roots, whose residues solve `X^2+uX+v=0`. This residual quadratic is separable.

Write the leading parts of A,B,C as `A_inf/s,B_inf/s,C_inf/s`. Then the P roots consist of one root

    A_inf/s + O(1)

and two finite roots solving `A_inf X^2+B_inf X+C_inf=0`. Here `A_inf` and `B_inf` are nonzero generic functions, and the latter quadratic is separable. Hensel lifting of these quadratics and the simple large roots shows that the full splitting extension is unramified at this generic infinity valuation. In particular, these are **poles of order one in E**, not poles whose orders have silently been multiplied by wild ramification.

By Matrix fact I, `A_inf` is a nonconstant affine-linear function of u,v. By the product Galois group (9), every pair of labels can be the large P root and the large Q root at a suitable place above infinity.

Let the ordered roots be `x_1,x_2,x_3` of P and `y_1,y_2,y_3` of Q. For any nonzero vector of constant coefficients in k, consider

    F = sum_i lambda_i x_i + sum_j mu_j y_j.              (10)

Choose a place where large-root labels i,j have at least one of `lambda_i,mu_j` nonzero. Its pole coefficient is

    lambda_i A_inf + mu_j.

It is nonzero: `A_inf` is nonconstant. Thus F has a simple pole. In particular,

    F is not g^2+g+constant in E.                         (11)

This proves more than the absence of one suspected relation. **Every** nonzero constant linear combination of the six root functions is Artin–Schreier nontrivial.

For r independent forms `L_1,...,L_r`, the `6r` classes `L_j x_i, L_j y_i` are therefore independent over F_2 modulo Artin–Schreier coboundaries and constants. Every nonzero binary combination gives a nonzero coefficient vector in (10).

## 4. Uniform collision count with prescribed trace cells

Fix any six trace-cell labels. Choose constants of prescribed absolute trace and impose the corresponding `6r` equations

    z_ij^2+z_ij = L_j r_i + e_ij                         (12)

on X, where `r_i` denotes one of its six root functions. Section 3 proves that this degree-`2^(6r)` Artin–Schreier cover is geometrically integral. Its dimension is three and its defining degrees are bounded in terms of r only.

The bounded-degree Lang–Weil estimate gives `q^3+O_r(q^(5/2))` rational points on this cover. Each ordered root sextuple in its prescribed cells has exactly `2^(6r)` lifts, and other sextuples have none. Hence for a single cell assignment the ordered count is

    q^3/2^(6r) + O_r(q^(5/2)).                           (13)

Summing over cell labels in `C^6` yields

    E_S = rho^6 q^3 + O_r(q^(5/2)).                      (14)

For the half selector, the leading term is `q^3/64`, for each fixed nonscalar zeta.

We may require the six parameters to be pairwise distinct at a cost `O(q^2)`. Each extra diagonal is a proper divisor: the relevant difference of root functions already has a simple pole by Section 3. We may similarly remove any bounded set of parameter values at cost `O(q^2)` per value.

There is also no issue with quotient identifications. For fixed `h_0 in H`, `h_0 != 1`,

    theta+s = h_0(theta+t),       s,t in F_q             (15)

has at most one solution if h_0 is nonscalar. Subtract two solutions to see this. If h_0 is a nonidentity scalar, (15) has no solution because theta is not in F_q. Delete every parameter occurring in such an identification; there are `O(h)` of them. The quotient map is injective on all remaining parameters.

After these deletions, (14) still holds, and every counted sextuple has six **distinct quotient points**. It is a genuinely nontrivial cyclic strong-B3 collision, not a duplicate parameterization of a trivial equality.

Already this proves that every nonempty bounded-rank trace-cell union fails for all sufficiently large q. The retention bound needs the conditional estimate below.

## 5. Conditioning on one root: why the fibers remain geometrically integral

We need an upper bound on the number of collisions through a selected parameter. It is not enough to assume that the total count distributes evenly among vertices.

Fix a Q-root label to be t and write

    Q=(X+t)(X^2+uX+v).                                  (16)

The coefficient field with this one root adjoined is `k(t,u,v)`. From (9),

    Gal(E/k(t,u,v)) = C2 x S3.                          (17)

First we prove that E has no algebraic constants over `k(t)` other than `k(t)`. This is the point needed for geometric integrality of the generic t-fiber.

If the relative algebraic constant field were nontrivial, it would be a nontrivial Galois quotient of `C2 x S3`. This group is solvable and its abelianization is `C2 x C2`; every nontrivial quotient therefore has a quadratic quotient. A quadratic constant extension would have to be one of the following three sign subfields, with classes

    v/u^2,       B(P),       v/u^2+B(P).                 (18)

None is constant:

* At `u=0`, the class `v/u^2` has nonsquare leading coefficient v in `k(t,v)`. The class `B(P)` is regular there. Indeed, (16) at u=0 parametrizes the generic Q discriminant divisor, which differs from the P divisor. Every rational function of t is regular at this horizontal divisor. Thus neither the first nor the third class in (18) can equal a function of t modulo Artin–Schreier coboundaries.

* At any divisor above `d_P=0`, the extension obtained by adjoining the one Q root is unramified with separable residue extension, since `d_Q != 0` generically there. The nonsquare leading coefficient in (8), now for P, remains nonsquare in a separable residue extension. These divisors are horizontal over the t-line. Otherwise t would equal some constant t_0 on one of them, forcing the irreducible degree-two divisor `d_P=0` into the affine hyperplane `Q(t_0)=0`, which is impossible. Thus `B(P)` too cannot become a function of t modulo a coboundary.

This excludes all three possible quadratic constant fields. Since E is separably generated over `k(t)`, it is regular over `k(t)`. Consequently the generic ordered-root fiber is geometrically integral and retains the full group (17) over `overline(k(t))(u,v)`.

Next test the five remaining root functions at infinity in the u,v-plane. Put `u=1/s`, `v=w/s`. The two residual Q roots have one large root `1/s+O(1)` and one finite root. The large P root has leading coefficient

    A_inf(t,w) = alpha(t) + beta(t) w,
    beta(t) = ell_2 M_zeta(X+t).                         (19)

The polynomial beta(t) is not identically zero: its two coefficients are `ell_2 M_zeta(X)` and `ell_2 M_zeta(1)`, and their simultaneous vanishing would make zeta scalar. Hence `A_inf(t,w)` is nonconstant in w over `overline(k(t))`. The finite-root quadratics are generically separable, just as in Section 3.

The group `C2 x S3` permits every choice of the two large-root labels. The same simple-pole argument proves independence of all `5r` Artin–Schreier classes of the five unfixed roots, over the geometric generic fiber. Thus the fiber covers with any five prescribed cell labels are geometrically integral generically in t.

By geometric-integrality specialization, all but `O_r(1)` t have geometrically integral fibers of bounded degree. Bounded-degree Lang–Weil on these dimension-two fibers, and division by their `2^(5r)` Artin–Schreier lifts, now gives

    # ordered collisions with y_1=t and other roots in S
        = rho^5 q^2 + O_r(q^(3/2))                      (20)

outside that bounded exceptional set. The same conclusion for a fixed P root follows by interchanging P,Q and replacing zeta by its nonscalar inverse.

### Uniformity of the specialization step

The finite exceptional set in this argument is genuinely bounded independently of q, f, zeta, the forms, and the cell labels. Here is a finite-type justification, so the word “generic” is not hiding a q-dependent exceptional set.

For fixed r, put all coefficients of f, the quadratic representative of zeta, the L_j, and the constants in (12) in one universal parameter space over F_2. Invert `det M_zeta`, impose nonscalarity, and invert the finitely many nonzero binary sums of the L_j. These are finite-type open conditions. The generic-fiber proof above works for every admissible geometric specialization of these coefficients; it uses only the two matrix facts, invertibility, and independence of the L_j. It does not require f to stay irreducible after extending constants.

In the universal family over this parameter space times the t-line, the locus of non-geometrically-integral fibers is constructible (geometric-integrality specialization for finite-presentation morphisms). Its fiber over each coefficient specialization is finite, since the generic t-fiber was proved geometrically integral. Decompose that constructible locus into finitely many locally closed pieces. Each piece has a quasi-finite finite-type map to the coefficient parameter space. Such maps have a uniform bound on their geometric fiber cardinalities. This bounds the total number of exceptional t by a constant depending only on the fixed presentation, hence only on r. This is also obtainable from bounded-degree Noether specialization forms.

All these presentations have fixed dimension and degree for fixed r: the root equations have degree at most three, (12) degree two, and the nonvanishing discriminants can be removed by one extra inverse variable. Bounded-degree Lang–Weil consequently has uniform constants in both (13) and (20).

A single exceptional t accounts for only `O_r(q^2)` ordered collisions in the three-dimensional total space: fixing one nonconstant root function is a proper hypersurface section of bounded degree. Deleting all exceptional parameters therefore does not change the main term of (14).

## 6. Covering the collision hypergraph gives the retention factor

Remove from S the bounded exceptional sets in Section 5 and all quotient-identification parameters from Section 4. Call the remaining parameter set V. Then

    |V| = rho q + O_(r,h)(1),

and the quotient map is injective on V. Restrict to ordered collisions with six distinct parameters in V. Their number is

    E = rho^6 q^3 + O_(r,h)(q^(5/2)).                    (21)

For a fixed vertex t in V, sum (20) over the six positions. Its number of incident ordered collisions is at most

    Delta = 6 rho^5 q^2 + O_r(q^(3/2)).                  (22)

Let A be any cyclic strong B3 subset of the original quotient image. The deleted vertices

    D = {t in V : (theta+t)H notin A}

must meet every collision in (21). Counting ordered collisions, with their ordering multiplicities unchanged on both sides, gives

    |D| Delta >= E,
    |D| >= rho q/6 - O_(r,h)(sqrt(q)).                   (23)

The original image has only `O_(r,h)(1)` points not represented by V. Therefore

    |A| <= 5 rho q/6 + O_(r,h)(sqrt(q)),

as asserted. This is an upper bound only; no claim of attaining the factor 5/6 is made.

The obstruction uses collisions with six distinct quotient points, so it is valid a fortiori for strong B3, which also forbids collisions involving repeated summands. The finite audit below explicitly checks repeated summands rather than relying on this large-q simplification.

## 7. Index 13 and index 7

For `q=16^m`, `3` not dividing `m`, the order of q modulo 13 is three. Thus order-13 H lies in F_4096, has `H intersect F_q*=1`, and every nonidentity element is nonscalar. The quotient has size `(q^3-1)/13`. Substitution of `rho=1/2` into (3) proves (2):

    13(5/12)^3 = 1625/1728 = 0.9403935185... .

The hypothetical full half-selector ratio `13/8` is not merely reduced to a still-excessive value: even arbitrary cyclic strong-B3 pruning of that selector has asymptotic cubic ratio strictly below one.

For index seven, choose any q with `3` not dividing `log_2 q`. Then order-seven H is nonscalar and the same theorem applies. At density 5/8,

    7(25/48)^3 = 109375/110592 = 0.9889955873... .

More generally, (3) rules out an excessive cyclic strong-B3 pruning whenever

    h (5 rho/6)^3 < 1.                                  (24)

Every full nonempty bounded-rank trace-cell selector is ruled out, regardless of (24), by the positive main term in (14). For larger-density cell unions where (24) fails, the 5/6 bound alone does **not** rule out an excessive arbitrary pruning. Nor is any bound claimed here when the number of independent trace forms grows with q.

## 8. Exact diagnostic audits

Run

    sage Submission/characteristic_two_trace_quotient_audit.sage

The script writes `Submission/characteristic_two_trace_quotient_results.json` and checks the identities in Sections 1–2 symbolically or exactly in finite fields. An independent standard-library-only verifier can then be run without Sage:

    python3 Submission/characteristic_two_trace_quotient_verify.py

It rechecks all 46 small-field subset maxima by triple enumeration modulo 315 and all 49 saved polynomial certificates using its own binary-polynomial field arithmetic. Both programs were run successfully. The note is a mathematical proof, not a Lean formalization; no admitted declaration in `Spec.lean` is used.

### Exhaustive q=16, not a random search

Every nonzero L can be absorbed into theta by multiplying all points by L. A translation of the parameters then changes `Tr(Lt)=c` to `Tr(t)=0`. Thus it suffices to check all `4080` degree-three theta in F_4096 against the one eight-element trace-zero hyperplane.

Translations of theta by that hyperplane and binary Frobenius preserve the quotient strong-B3 property. Their exact orbits reduce the audit to **46 representatives**, whose orbit sizes sum to 4080. This covers all choices of theta,L,c, not just primitive theta or one cubic model.

The quotient is `Z/315Z`. The audit first deduplicates its point image and then enumerates **all unordered triple multisets, including repeats**, in that image. It also exhausts every subset of each image and independently checks the returned maximizers.

Weighted by the number of normalized theta:

| Quotient image size | Number of theta |
|---:|---:|
| 8 | 3768 |
| 7 | 288 |
| 6 | 24 |

| Maximum cyclic strong-B3 subset size | Number of theta |
|---:|---:|
| 6 | 3000 |
| 5 | 1032 |
| 4 | 48 |

No full half-trace image is strong B3. Every representative has a collision involving a repeated summand. Some do not have a six-distinct-point collision at this small q, which is why repeats must not be discarded in the exact audit.

For the first representative, theta is the primitive generator in the audit's explicit field model, and the quotient logarithms are

    {1,30,43,54,143,175,217,313} subset Z/315Z.

Two immediately checkable witnesses are

    1+43+175 = 1+1+217 = 219,
    30+43+143 = 216 = 1+217+313  (mod 315).

The latter uses six different quotient points. The JSON also gives the underlying field parameters, f, zeta, and its multiplication matrix for the exact polynomial certificate.

### Targeted q=256, fixed-field nonprimitive theta

The second diagnostic deliberately uses theta in `F_4096 \ F_16`, inside F_(2^24), and the affine selector `Tr_(256/2)(t)=1`. This selector contains **no** F_16 points, so this is not just inheriting the q=16 collision by including its parameter set.

Its image has 128 distinct points. Direct quotient-product enumeration of all `binom(130,3)=357760` triple multisets finds:

* 314546 different triple-product classes;
* 46732 unordered pairs of distinct triple multisets with equal quotient product;
* maximum triple-product multiplicity 5;
* both a six-distinct-point witness and a repeated-summand witness.

The witness ratios have order 13. Their monic cubics are checked against the exact transformation (5), using zeta's quadratic representative modulo f. No discrete-log heuristic, approximate arithmetic, or random search is used.

## Conclusion

The nonscalar characteristic-two case has two separate pole checks: a **nonremovable nonsquare double pole** separates the cubic sign fields, and **unramified simple poles at infinity** eliminate every trace relation on their compositum. Conditioning on a root preserves geometric integrality and yields the uniform 5/6 deletion obstruction.

Consequently the specified index-13 half-trace route fails, including its fixed-field-theta specializations and arbitrary cyclic strong-B3 pruning. The analogous index-seven density-5/8 trace-cell route also falls below cubic ratio one. The original integer strong-B3 asymptotic remains unresolved; `Spec.lean` is unchanged.
