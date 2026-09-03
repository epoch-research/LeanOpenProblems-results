# Characteristic five: a proved obstruction for the Artin–Schreier twist

## Result and scope

The degree-five Artin–Schreier candidate does **not** give a full or almost-full cyclic strong-B3 set. Wild exceptional arithmetic monodromy cannot rescue it, even after arbitrary `o(q)` deletions.

Here is a uniform form of the result. Let

- `q = 5^m`, with `m` odd;
- `K = F_(q^3)`, and let `theta` have degree three over `F_q`;
- `H` be any fractional linear transformation over `F_q`;
- `F(t) = a (H(t)^5 + c H(t) + d)`, where `a != 0` and `c,d in F_q`.

At the finite parameters where `F` is defined and nonzero, put

    phi_F(t) = (theta+t)/(theta^q+t) * F(t)^2,
    M = (q^3-1)/2.

**Theorem.** These points are distinct and lie in a genuinely cyclic group of order `M`. Uniformly in all the displayed choices, at least

    q^3/648 - O(q^(5/2))                                      (1)

of its elements have two representations as products of three distinct points, with **six distinct parameters** between the two representations. Consequently every parameter subset `S` for which `phi_F(S)` is strong B3 satisfies

    |S| <= (323/324) q + O(sqrt(q)).                            (2)

The implicit constants are absolute for this bounded-degree family. In particular, the full `q+O(1)` set and every set obtained from it by `o(q)` deletions fail strong B3 for all sufficiently large `q`.

The statement also holds after replacing `F` by its reciprocal, multiplying it by a nonzero constant, or raising it to a `5`-power, including iterated `5`-powers. These operations preserve the exact collision relation below. Thus the result includes

    t^5-t-a,        t^5+ct+d,
    (1/t)^5-(1/t)-a,
    1/(H(t)^5+cH(t)+d),

and the corresponding Möbius changes of parameter. For `t^5-t-a`, the condition `Tr_(F_q/F_5)(a) != 0` indeed makes all `q` finite parameters admissible.

This is an obstruction to the proposed **near-full** construction, not a proof that every smaller subset has cubic ratio at most one. It does not settle the general B3 asymptotic problem. No admitted declaration or previous obstruction theorem is used; the proof is given here. The standard finite-cover Chebotarev/Lang–Weil estimate used for counting is stated explicitly in Section 7. `Spec.lean` is unchanged.

## 1. Cyclic transfer and the exact multiset criterion

Write `alpha=-theta`, and let `f` be its monic irreducible cubic. This sign convention permits the parameters themselves to be roots of the cubics below.

Let `T_1 = ker(N_(K/F_q))`, of order `q^2+q+1`. Since `m` is odd,

    gcd(q^2+q+1,q-1) = gcd(3,q-1) = 1.

Thus multiplication identifies

    T_1 x (F_q^*)^2

with the norm-square subgroup of `K^*`. Its order is `M`; it is cyclic, being a subgroup of `K^*`. There is no noncyclic product-group substitution here.

For a parameter triple, **with repetitions allowed**, let

    P(X) = product_i (X-t_i),
    R(P) = product_i F(t_i).

For a polynomial `F`, `R(P)=Res(P,F)`. For `F=A/B`, it is `Res(P,A)/Res(P,B)`. The norm-one component of its product is

    P(alpha)/P(alpha)^q.

Equality of two products is therefore equivalent to both

    P(alpha)/Q(alpha) in F_q^*,       R(P)^2=R(Q)^2.           (3)

Since `P,Q` are monic cubics, the first condition is exactly

    P = f + lambda (Q-f),       lambda in F_q^*.             (4)

Equivalently, after choosing a representative `U` of a projective direction of polynomials of degree at most two, all candidates lie in the cubic pencil

    P_lambda = f + lambda U.                                 (5)

The scalar condition is `R_U(lambda)^2=R_U(mu)^2`.

The same direct-product argument for one-point products shows that `phi_F(t)=phi_F(u)` implies `(alpha-t)/(alpha-u) in F_q^*`, hence `t=u`. Passing to logarithms with respect to a generator of the subgroup of order `M` preserves exactly the multiset product relation, so (3) is a strong-B3 criterion in `Z/MZ` as well.

Two different rational cubics in (5) cannot share a rational root: a common root would satisfy both `f(r)=0` and `U(r)=0`. Thus two distinct, completely split, squarefree cubics in the same pencil automatically give six distinct parameters.

## 2. The actual quintic resultant

For

    P=t^3+b2 t^2+b1 t+b0,       F=t^5+c t+d,

reduce `F` modulo `P`. In characteristic five it is `A t^2+B t+C`, where

    A = -b2^3+2b2 b1-b0,
    B = -b2^2 b1+b1^2+b2 b0+c,
    C = (b1-b2^2)b0+d.

Consequently the actual resultant, not an unspecified degree bound, is

    R(P) = det [ C    -A b0           A b2 b0-B b0              ]
               [ B     C-A b1        A(b2 b1-b0)-B b1          ] .   (6)
               [ A     B-A b2        C-B b2+A(b2^2-b1)         ]

These are the columns of multiplication by `F` on `F_q[t]/(P)` in the basis `1,t,t^2`.

A compact closed form results after depressing the cubic. If `P=t^3+A t+B`, then

    R(P) = -B^5 + c A B^3 + 2 c d B^2
           -c(A^2+c)^2 B + d A(A^2+c)^2 + d^3.               (7)

In particular, for `F=t^5-t-a` and the depressed cubic `P=t^3+A t+B`,

    R(P) = -B^5-A B^3+2a B^2+(A^2-1)^2 B
           -a A(A^2-1)^2-a^3.                              (7a)

For a general cubic, formula (7) applies after the substitutions

    A = b1-2b2^2,
    B = b0-2b2 b1+b2^3,
    d_new = d+3b2^5+3c b2.

The audit verifies (6), (7), and this substitution as polynomial identities in characteristic five.

For example, for a constant pencil `P_lambda=t^3+A t+(B+lambda)`, putting `z=B+lambda` gives (7) with `B=z`, and

    R'(z) = 3cA z^2+4cd z-c(A^2+c)^2.                       (8)

The quadratic discriminant in (8) is

    c^2 [d^2+2A(A^2+c)^2].                                  (9)

Thus particular pencils can have special critical-point behavior. The proof below does not assume a Morse quintic or full `S5` monodromy.

More generally, if `c!=0` and `r_1,...,r_5` are the distinct roots of `F`, then

    R_U(lambda) = - product_j (f(r_j)+lambda U(r_j)).          (10)

When `f` and `F` have no common root, the five zeros in (10) are distinct for a generic `U`: equality of any two is a nonzero linear equation in the coefficients of `U`. Hence `R_U` has degree five and is a separable map. Crucially,

    deg_lambda R_U' <= 3                                    (11)

because the derivative of its leading fifth power vanishes.

For `H=A/B` fractional linear, the rational variant has

    F = (A^5+cAB^4+dB^5)/B^5,
    R_U = Res(P_lambda,A^5+cAB^4+dB^5)
          / Res(P_lambda,B)^5.                              (12)

The denominator is the fifth power of a linear function of `lambda` (or is constant). There is generically no cancellation. Thus `R_U : P^1 -> P^1` has a **single pole of order five**, rational over the function field of the pencil directions. Moving that pole to infinity makes it a separable polynomial of degree five over that function field. Assertion (11), and its branch-value consequence, apply in this coordinate too.

## 3. A primitive degree-four doubled-root cover

This geometric lemma supplies the ordering information without a prior tame-obstruction theorem.

Work over an algebraically closed field `k` of characteristic five. Let `V` be the four-dimensional space of binary cubics, and let `f` have three distinct projective roots. Projecting `P(V)` from `[f]` gives the pencil-direction plane

    Pi = P(V/<f>) = P^2.

Let `D` be the normalization of the discriminant surface of binary cubics. Its parameters are

    (x,y) in P^1 x P^1,       P = l_x^2 l_y,

where `l_x` is a linear form vanishing at `x`. The discriminant surface has degree four and `[f]` is outside it. Therefore projection gives a finite cover

    pi : D -> Pi,       deg(pi)=4.                           (13)

It is generically separable, since its degree is four and the characteristic is five.

For each `x`, the cubics with double root `x` form a projective line `L_x` in `P(V)`. Its projected image is a line `ell_x` in `Pi`, and projection maps `L_x` isomorphically onto `ell_x`. For `x!=z`, the lines `L_x,L_z` are skew: a nonzero cubic cannot be divisible by both `l_x^2` and `l_z^2`. Their projected lines cannot coincide, since that would put both original lines in the projective plane over the same projected line. Hence

    ell_x != ell_z whenever x!=z.                            (14)

An ordered pair of distinct points of a generic fiber of (13) is now parametrized birationally by `(x,z)`, `x!=z`: its direction is the unique intersection `ell_x intersect ell_z`, and the two cubics are then determined. The off-diagonal fiber product of (13) is therefore irreducible. Equivalently, its geometric monodromy is **2-transitive** on four letters, and in particular primitive. There is no proper intermediate field between `k(Pi)` and `k(D)`.

In affine coordinates one can check the same construction using

    W_U(x) = f'(x)U(x)-f(x)U'(x).

Its four generic roots are the doubled roots of pencil members. For the normalization `f=x^3-x`,

    W_U = u2 x^4+2u1 x^3+(u2+3u0)x^2-u0.

The critical-line map is `[x^4+x^2 : 2x^3 : 3x^2-1]`. The audit also verifies that its coordinates have no quadratic relation. The geometric skew-line argument above works for every squarefree `f`, not just this normalization.

### The scalar distinguishes all four generic doubled-root cubics

Let `F` be a nonconstant rational function whose zeros and poles are disjoint from the roots of `f`. On `D`, put

    r_D(x,y)=F(x)^2 F(y).

This function is **not** in `k(Pi)`. Here is a divisor proof that also handles positive characteristic.

Choose a zero `a` of `F`. The zero curve `x=a` maps isomorphically onto the line `ell_a`. For a generic point of that curve, `pi` is unramified. In affine coordinates this follows from

    W_U'(a)=P''(a)U(a) != 0

for `P=(t-a)^2(t-y)`, generic `y`, and `f(a)!=0`; the argument is coordinate invariant if `a=infinity`. Thus this is just one of the four generic sheets above `ell_a`.

The other zero curves of `r_D` are `x=b` or `y=b`, for zeros `b` of `F`. Curves `x=b`, `b!=a`, map to different lines by (14). A curve `y=b` maps to a smooth conic: it is the conic of cubics `l_b l_x^2` in the plane of cubics divisible by `l_b`, and projection is an isomorphism on that plane because `f(b)!=0`. No such conic is the line `ell_a`. The same description for poles shows that the other sheets above a generic point of `ell_a` have finite, nonzero `r_D`.

A function pulled back from `Pi` could not vanish on just one of these sheets. This proves the assertion. By primitivity of (13),

    k(Pi)(r_D)=k(D),       [k(Pi)(r_D):k(Pi)]=4.             (15)

The square also generates the field. Indeed, primitivity leaves only `k(Pi)` or `k(D)` as possibilities for `k(Pi)(r_D^2)`; the former would make `r_D` at most quadratic over `k(Pi)`, contradicting (15). Hence

    k(Pi)(r_D^2)=k(D).                                      (16)

In particular, the image of the doubled-root divisor under the squared scalar map has exactly one generic doubled-root sheet above it. The two unsquared divisors with scalar values `r_D` and `-r_D` are distinct.

## 4. Why the Artin–Schreier family meets the coprimality hypothesis

For `c!=0`, the five roots of `t^5+ct+d` over an algebraic closure form

    beta + delta F_5,       delta^4=-c.

The `q`-Frobenius acts on their labels as an affine permutation of `F_5`. Its cycle type is one of

    1^5,       5,       1+2+2,       1+4.

There is no cycle of length three. Consequently this quintic has no irreducible cubic factor over `F_q`, so it is coprime to every irreducible cubic `f`. A Möbius transformation over `F_q` preserves root-orbit lengths, and its unique pole is rational. Thus the rational variants also have zeros and poles disjoint from the roots of `f`.

For `t^5-t-a`, Frobenius is translation by `Tr_(F_q/F_5)(a)` on the five roots. Nonzero trace gives one orbit of length five, proving both irreducibility and the absence of rational zeros.

If `c=0`, perfection of the finite field gives

    H(t)^5+d = (H(t)+d^(1/5))^5.

For rational parameters, equality of the squared triple products is equivalent to equality for the fractional linear function `H(t)+d^(1/5)`, since fifth powering is bijective on `F_q^*`. We use this degree-one scalar map instead. Its numerator and denominator also avoid the roots of `f`. This covers the genuinely inseparable scalar case rather than silently applying separable monodromy to it.

## 5. Excluding fierce ramification at the required divisor

Set `E=k(Pi)`. In the `c!=0` case, choose a coordinate `z` on the scalar pencil so that `R(z)` is a separable polynomial of degree five, as in (10) or (12). Its finite branch values are supported on

    C(s) = Res_z(R(z)-s,R'(z)) in E[s],
    deg_s C <= 3.                                          (17)

In contrast, (15) says that the minimal polynomial of the doubled-root scalar value `r_D` over `E` is irreducible of degree four. So is the polynomial for `-r_D`. Neither can divide (17).

This proves more than an assertion about ramification indices. Localize `E[s]` at either of those degree-four primes. The polynomial `R(z)-s` has unit leading coefficient and unit discriminant there. Its root algebra is **finite étale** over that local ring. All residue extensions are separable, and every ramification index is one. In particular, an `e=1` extension with purely inseparable residue of degree five — fierce ramification — is impossible at these primes.

The square map `s -> s^2` is étale at the generic points in question. Equations (15)–(16) identify its two pullback divisors as the ones just checked. Therefore the full unordered map with scalar `R^2` is unramified at **every** sheet above the image of the doubled-root divisor. Exactly one sheet has a double cubic root.

For `c=0` after the degree-one reduction, the same conclusion is immediate, since a degree-one scalar map has no branch values.

There may certainly be wild ramification at the order-five pole of the quintic map. It is not being denied or made tame by assumption. It is irrelevant to this divisor. The degree-four versus degree-three comparison is precisely what closes the proposed characteristic-five gap for the one-pole family.

## 6. Independent ordering groups

Let `X` be the open space of monic cubics on which the pencil direction and scalar are defined. Its squared map to `Pi x G_m` has degree

    N=10       if c!=0,
    N=2        after the c=0 reduction.

Both maps are generically separable and have geometrically irreducible source. Ordering the three roots gives the usual `S3` extension of the function field of `X`.

Let `G_0` be the geometric monodromy of the unordered map and `G` that of the normal closure with all roots ordered. There are `N` cubic blocks, and

    G <= S3 wr G_0.

Section 5 supplies a valuation at which the unordered map is étale on all sheets and exactly one cubic has one ordinary double root. In the ordered normal closure its inertia is a **single transposition in a single cubic block**, fixing every other block. It lies in the kernel of `G -> G_0`.

Conjugation moves its support to each block, since `G_0` is transitive. The stabilizer of a block surjects onto the full `S3` of that universal cubic. Conjugating within this stabilizer produces every transposition in that block, still supported only there. These generate the full symmetric group in each block. Hence

    ker(G -> G_0) = S3^N.                                   (18)

All these factors are geometric. No claim that the scalar quintic itself has geometric or arithmetic group `S5` is needed.

## 7. Arithmetic exceptional monodromy still cannot give unique triples

Consider the arithmetic monodromy of the unordered squared map. The intermediate square cover `s^2=w` divides its `N` sheets into two sets of size `N/2`. Its geometric sign quotient is `C2`; the geometric subgroup preserving the two signs is transitive on each sign set, because the unsquared source is geometrically irreducible.

In the arithmetic Frobenius coset, exactly half the elements preserve the two sign sets. Fix one such element `gamma`, and let `H_0` be the sign-preserving geometric subgroup. The elementary coset form of Burnside's count gives

    average_(h in H_0) #Fix(gamma h) = 2.                   (19)

Indeed, each of the two transitive `H_0`-orbits contributes one to the average, and `gamma` preserves both. Since there are at most `N` fixed blocks, at least a proportion `1/(N-1)` of this half-coset has at least two fixed blocks: otherwise an average of two would be impossible.

Lift to the ordered arithmetic group. By (18), and because the entire kernel is geometric, the root permutations in any specified two fixed blocks are independently uniform in `S3`. A fraction `1/36` of the lifts make both permutations the identity, so both cubics split completely. Therefore the fraction of the full Frobenius coset with at least two fully split cubic blocks is at least

    1 / [2 (N-1) 36] >= 1/648.                             (20)

This remains true if the quintic's arithmetic action is exceptional. The square cover and independent ordering factors, not a supposition about quintic Frobenius cycle types, force the collision.

### The counting input and uniformity

We use the following standard consequence of Lang–Weil, often called finite-cover Chebotarev. For a finite étale cover of a geometrically irreducible three-dimensional rational base over `F_q`, take its arithmetic normal closure. If `C` is a conjugacy-invariant subset of the appropriate Frobenius coset, the number of rational base points with Frobenius in `C` is

    (|C|/|G_geom|) q^3 + O(q^(5/2)).                        (21)

The error is uniform when the defining degrees and dimensions of the cover and the removed closed sets are bounded. One obtains (21) by applying Lang–Weil to the Frobenius twists of the geometric components of the normal closure and counting points in each fiber. The coset, rather than the geometric group alone, is essential when the normal closure has a nontrivial constant field.

Here all these complexities are bounded absolutely: the scalar degree is at most ten, each ordered cubic has degree six, and the normal closure can be realized using boundedly many scalar roots and ordered cubic roots. Its group has order at most `6^10 * 10!`. Removing branch divisors, zero/pole loci, common-root loci, and points at infinity costs only bounded-degree closed sets. Thus (21) applies uniformly even when `f,c,d,H` vary with `q`.

Apply (21) to the property in (20). On the chosen open set the split cubics have three distinct finite admissible roots. Different cubics in the same pencil have disjoint rational root sets by Section 1. The target points have square scalar coordinate and correspond injectively to elements of the cyclic group: `[U]` maps bijectively on rational points to the norm-one factor via `U(alpha)/U(alpha)^q`, and the scalar lies in `(F_q^*)^2`. This proves (1).

The degree-one reduction for `c=0` actually gives the larger proportion `1/72`; the weaker uniform bound `1/648` suffices. Fifth powering of the scalar target is a bijection on rational points, so the bound transfers back to the original inseparable expression.

## 8. Arbitrary deletions and the strong-B3 convention

Let `B_q` be the number of product values in (1). Each has at least two disjoint squarefree triple representations. A strong-B3 subset must destroy at least one of these representations for every such value.

Deleting one parameter affects at most

    binomial(q-1,2)

product values represented by a squarefree triple containing that parameter. Therefore, if `r=q-|S|` parameters are absent, necessarily

    r * binomial(q-1,2) >= B_q
      >= q^3/648 - O(q^(5/2)).

This yields (2). Originally inadmissible zeros or poles are only `O(1)` parameters and do not affect the conclusion.

All exact criteria in Section 1 allow repeated roots. The negative proof produces the stronger six-distinct-root obstruction, so it cannot be evaded by changing how repeated triples are treated. The finite audit below explicitly includes all repeated triples as a separate check; no positive B3 certificate is inferred from checking only distinct triples.

## 9. Reproducible targeted audit

Run

    sage Submission/wild_artin_schreier_b3_audit.sage

The script is deterministic. It checks the universal resultant identities, the critical-point quartic, and the lack of a quadratic relation for the critical-line map. It then fixes

- `q=5`, `f=t^3+t+1`;
- `q=125`, `F_q=F_5[b]/(b^3+3b+3)`, `f=t^3+t+b+1`;

and audits `t^5-t-1`, `t^5+t+1`, and `(1/t)^5-(1/t)-1`. The inseparable case `t^5+1` is also checked at `q=5`.

For each case it enumerates **all triple multisets**, verifies both directions of the projective/scalar-versus-cyclic-log criterion, checks actual resultants on deterministic samples, and records explicit witnesses. The `q=5` cases include an exhaustive audit of every parameter subset. Fixed pencil diagnostics record `R`, `R'`, the cubic discriminant, and its scalar-value resultant. Specialized pencils can degenerate; they are not substituted for the generic proof above.

Results are in `Submission/wild_artin_schreier_b3_audit.json`. All assertions passed. Across the seven cases, **984,470 triple multisets** were checked. A further two-direction calculation over `F_5(u,v)`, with `P_z=t^3+t+1+z(t^2+ut+v)`, verifies degrees `deg R=5`, `deg R'=3`, and `deg Disc(P_z)=4`. In its quartic discriminant algebra, both `1,R,R^2,R^3` and `1,R^2,R^4,R^6` have rank four.

| q | F | Admissible parameters | Triple multisets | Product values with a collision | Values with two squarefree triples |
|---:|---|---:|---:|---:|---:|
| 5 | `t^5-t-1` | 5 | 35 | 8 | 0 |
| 5 | `t^5+t+1` | 4 | 20 | 1 | 0 |
| 5 | `(1/t)^5-(1/t)-1` | 4 | 20 | 2 | 0 |
| 5 | `t^5+1` | 4 | 20 | 1 | 0 |
| 125 | `t^5-t-1` | 125 | 333,375 | 44,163 | 40,496 |
| 125 | `t^5+t+1` | 124 | 325,500 | 42,488 | 38,978 |
| 125 | `(1/t)^5-(1/t)-1` | 124 | 325,500 | 42,475 | 38,876 |

Every `q=5` case has maximum strong-B3 subset size three. For the zero-free Artin–Schreier case, a repeated-triple collision is

    {0,0,0} versus {1,1,3}.

Here `P=t^3`, `Q=t^3+2t+2`, `P=f+4(Q-f)`, and `R(P)=R(Q)=4`. The subgroup has order 62.

For `q=125`, write `b^3+3b+3=0`, take `f=t^3+t+b+1` and `F=t^5-t-1`. An explicit six-distinct-root collision is

    {0, b^2+4, b^2+b+4}
        versus
    {1, b, 3b^2+b+2}.                                      (22)

The associated monic cubics are

    P=t^3+(3b^2+4b+2)t^2+(3b+3)t,
    Q=t^3+(2b^2+3b+2)t^2+(4b^2+3)t+4b^2+2b+4.

They satisfy

    P=f+(b^2+4b)(Q-f),
    R(P)=R(Q)=b^2+b+4.

In the audited cyclic group of order `976562`, the two triples of logs are

    {853182,898653,226683},
    {129332,564279,308345},

both summing to `25394` modulo `976562`. The JSON records the extension-field modulus, `theta`, and the generator as well.

The identities in (22) persist over every `F_(125^r)` with `r` odd and `gcd(r,15)=1`, using the same `f` and `F`: the cubic remains irreducible and `Tr(1)=3r != 0` in `F_5`. Thus this is also an explicit collision in an unbounded extension family, independently of the general asymptotic counting argument.

The audit deliberately records special-pencil degeneracies: for example, `U=1` has a sign coincidence among doubled-root scalar values in both audited fields, and `U=t^2+t+1` at `q=5` has a branch-value coincidence. Neither contradicts the generic two-direction argument; neither is hidden by choosing only nondegenerate sample pencils.

## 10. What this does and does not close

The whole polynomial family `t^5+ct+d`, and the one-pole Artin–Schreier rational variants described above, are rigorously excluded as full or `q-o(q)` cyclic strong-B3 constructions. The `e=1` inseparable-residue possibility is explicitly ruled out at the needed doubled-root divisor, not assumed away.

This proof does not classify arbitrary quotients of two independent Artin–Schreier polynomials, nor rational substitutions of degree greater than one, nor general rational functions of higher degree. For those families the single-pole degree-five branch bound (17) need not apply. Nothing here asserts a general wild extension of a tame-obstruction theorem, and nothing here disproves the possibility of a substantially smaller B3 subset with some cubic excess. A negative cyclic result is also not automatically an obstruction to every possible integer lift; only the cyclic strong-B3 claim is being excluded.
