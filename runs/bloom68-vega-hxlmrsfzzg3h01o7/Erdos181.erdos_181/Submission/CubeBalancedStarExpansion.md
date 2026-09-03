# Balanced neighbourhoods: an exact fourth-order audit of a global expansion

## Outcome

**No proof or disproof of `R(Q_d)=O(2^d)` is obtained.** Neither admitted theorem was used, and `Spec.lean` is unchanged. This is a focused new attempt at the all-order balanced-relation route, not a conditional Ramsey theorem.

The new result is a precise failure of the attempted *absolute centered-expansion closure*. For every fixed integer `K>=16`, there are symmetric zero-one relations with exactly constant one-coordinate bad probability `p_d<1/K` such that:

* the sum of pair correlations around a cube neighbourhood is bounded;
* the sum over just the rooted four-neighbourhood stars of their fourth centered moments, and separately of their fourth joint cumulants, is
  
  `d/K^3 + O_K(1)`;
* the same asymptotic holds under uniform **injective** sampling of the source labels.

Thus small first-coordinate-balanced bad probability and two-vertex neighbourhood overlaps do not give the dimension-uniform absolute root-sum bound attempted below. This is not a failure of the arbitrary balanced packing assertion: these particular relations have explicit avoiding injections. They are not graph countercolourings, nor are they asserted to arise from the edge-fugacity minimizer. In particular this does not refute EL.

## 1. The proposed complete avoidance argument

Let `E,O` be the two parity classes of `Q_d`, with `m=2^(d-1)`. Each odd centre `y` gives the `d`-set `e_y=N_Q(y)` of even source vertices. Distinct neighbourhoods either are disjoint or intersect in two vertices; intersection occurs exactly when their centres have Hamming distance two. The dependency graph on centres consequently has degree `binomial(d,2)`.

Let `B` be a coordinate-permutation-invariant zero-one relation on `Omega^d`, and suppose

`Pr(B(X_1,...,X_d) | X_1=a)=p`

for every `a`, for independent uniform coordinates (repetitions allowed). Initially sample the even source labels independently in `Omega`. Set

`g_y=(1_B(X|e_y)-p)/(1-p)`.

Then the **full**, not truncated, avoidance partition is exactly

`Z_iid=(1-p)^m sum_{S subset O} (-1)^|S| E product_{y in S} g_y`.       (1)

Independence on disjoint sets of source variables factors each moment across the connected components of `S` in the neighbourhood dependency graph. Thus (1) is a hard-core polymer partition with connected-set activities

`w(S)=(-1)^|S| E product_{y in S} g_y`.

The attempted closure was to use symmetry and balance to obtain dimension-uniform small absolute rooted activity sums and then apply signed-partition positivity. This would still need a collision-accounted version for ordinary injections. Both limitations matter: positivity for (1) alone is not an injective embedding theorem.

### The pair estimate really is dimension-uniform

Write `g=(1_B-p)/(1-p)` on one independent `d`-tuple and

`h(a,b)=E[g | X_1=a, X_2=b]`.

Balance implies `E[h(a,X_2)]=0`. The functions `h(X_i,X_j)` for distinct unordered pairs are orthogonal: disjoint pairs are independent, and for pairs meeting in one coordinate, conditioning on that coordinate gives zero. Also

`E[g h(X_i,X_j)]=E[h(X_i,X_j)^2]`.

The orthogonal projection onto their sum therefore gives

`binomial(d,2) E h^2 <= E g^2 = p/(1-p)`.                    (2)

For two intersecting cube neighbourhoods, condition on their two common source variables. The other variables are independent, and symmetry identifies both conditional means with `h`. Hence

`E[g_y g_z]=E h^2 >=0`,

and summing (2) over the `binomial(d,2)` neighbours of one centre gives the desired bounded pair load. No conditional marginal after avoidance was substituted here.

The next sections test the **actual higher-order moments**, rather than extrapolating (2).

## 2. A simple exactly balanced relation

Fix integers `K>=16`, `d>=8`, and put

`q=1/(Kd)`, `u=1-q`, `v=1-2q`,

`p=1-u^(d-1)`, `w=(u/v)^(d-1)-1`.

There are three types `A,S,T` of probabilities `q,q,v`. Define a symmetric weighted type relation `W` as follows:

* `W=1` if the tuple contains both an `A` and an `S`;
* `W=0` if it contains at least one rare type but not both;
* `W=w` if all its coordinates have ordinary type `T`.

Equivalently, with `a_i=1_{type_i != A}`, `b_i=1_{type_i != S}`, and `o_i=1_{type_i=T}`,

`W = 1 - product_i a_i - product_i b_i + (1+w) product_i o_i`.       (3)

The parameters are valid. Bernoulli's inequality applied to

`(u/v)^(d-1)=(1-q/u)^(-(d-1))`

gives

`0<w <= (d-1)q/(1-dq) <=1/(K-1)<1`,

while `0<p<(d q)=1/K`.

The conditional mean at either rare type is `1-u^(d-1)=p`. At the ordinary type it is

`1-2u^(d-1)+v^(d-1)+w v^(d-1)=p`.                         (4)

Thus `W` is exactly one-coordinate balanced, not approximately balanced.

### An actual symmetric zero-one lift

Take a type alphabet of size `Kd`, with one letter of type `A`, one of type `S`, and the other `Kd-2` of type `T`. Put

`L=(Kd-2)^(d-1)`, `r=(Kd-1)^(d-1)-L`, so `r/L=w`.

For any positive integer `s`, let

`Omega=[Kd] x (Z/LZ) x [s]`, `N=Kd L s`.

Ignore the last coordinate. A tuple is bad if it contains both rare types, or if all its types are ordinary and the sum of its tags modulo `L` lies in `{0,...,r-1}`. Otherwise it is good.

This is a genuine symmetric zero-one relation. Given any one full coordinate, there is at least one other independent uniform tag, so the all-ordinary conditional bad probability is exactly `r/L=w`. Equation (4) proves exact one-coordinate balance for **every full host value**. This includes repeated input values in the sampling convention.

The alphabet can be made arbitrarily large by increasing `s`. Its size is generally much larger than `2^d`; no claim of a counterexample at a fixed linear host size is made.

## 3. Four cube neighbourhoods around one even hub

Fix an even vertex `x`, and distinct coordinates `i_1,...,i_t`, with `t<d`. Use the odd centres

`y_j=x xor e_(i_j)`.

Their shared variables consist of:

* the common even hub `x`;
* one variable `z_ij=x xor e_(i_i) xor e_(i_j)` for each pair `i<j`;
* `d-t` private variables in each neighbourhood.

The private variables for different centres are disjoint. In the zero-one lift, their private tags let us integrate the tag constraint **independently in each factor**, even after all shared types and tags have been fixed. This is why `t<d` is imposed. Averaging the private types in (3) then gives the exact conditional normalized factor

`1 - u^(1-t) a_x product_{j != i} a_ij`

`  - u^(1-t) b_x product_{j != i} b_ij`

`  + v^(1-t) o_x product_{j != i} o_ij`.                   (5)

The `d`-dependence has disappeared except through `q`. This calculation concerns the actual zero-one relation, not only its weighted surrogate.

### Conditional moment at a rare hub

If the hub has type `A` (or `S`), one of the two negative terms survives and the last term vanishes. For example, at type `A`, (5) is

`1-u^(1-t) product_{j != i} 1_{type(z_ij) != S}`.

Expanding over selected centres, a selected set of size `j` constrains exactly `(t-1)j-binomial(j,2)` pair variables. Its normalized contribution is `u^(-binomial(j,2))`. Therefore the exact conditional moment is

`A_t(q)=sum_{j=0}^t (-1)^j binomial(t,j) u^(-binomial(j,2))`.          (6)

In particular,

`A_4(q)=-3+6/u-4/u^3+1/u^6 = 3q^2+O(q^3)`.                         (7)

The leading term comes from shared rare pair variables; treating the centres as independent after fixing the hub would erase it.

### Conditional moment at an ordinary hub

An exact finite expression is useful for independent verification. Let `a,b,c,z` be the numbers of centres choosing, respectively, the first negative term, the second negative term, the last term, and the constant in (5); thus `a+b+c+z=t`. Then

`T_t(q) = sum t!/(a!b!c!z!) (-1)^(a+b)`

`             * u^((1-t)(a+b)+binomial(a,2)+binomial(b,2)+z(a+b))`

`             * v^((1-t)c+binomial(c,2)+c(t-c)+ab)`.        (8)

Indeed, a pair variable restricted by the same one-sided type condition at both ends has probability `u`, opposite one-sided restrictions have probability `v`, and an ordinary-type restriction forces probability `v`. These account for every edge of the complete graph on the `t` centres.

For clarity, `T_4(q)=O(q^4)` also has a short proof without simplifying (8). On the six pair variables of the four-star, call a variable rare if its type is `A` or `S`. At a centre with no incident rare variables, (5) equals `1-2/u^3+1/v^3=O(q^2)`. With just one rare type present it equals `1-u^(-3)=O(q)`, and with both rare types it equals `1`.

If `R` of the six pair variables are rare, their assignment has probability `O(q^R)`. Write `s_i` for the number of rare variables incident with centre `i`, so `sum s_i=2R`. The product of its four factors is

`O(q^(sum_i max(2-s_i,0)))`.

For `R<=4` the total exponent is at least `R+8-2R=8-R>=4`; for `R>=4` the probability alone supplies exponent at least four. There are only `3^6` type assignments. This proves the asserted bound with a constant independent of `d`.

## 4. The fourth-order root load diverges

Let `M_t` be the joint moment for the `t` centres. Equations (6)--(8) give

`M_t(q)=2q A_t(q)+v T_t(q)`.                               (9)

The pair case simplifies exactly to

`M_2(q)=2q^2/u^2`.                                        (10)

For four centres, (7)--(9) prove

`M_4(q)=6q^3+O(q^4)`.                                     (11)

All individual means are zero and all six pair moments equal (10). Hence the fourth joint cumulant is

`kappa_4(q)=M_4(q)-3M_2(q)^2 = 6q^3+O(q^4)`.               (12)

These are exact asymptotic consequences of rational identities, not numerical fits. As a quantitative check one can simplify (12) to

`kappa_4(q)=2q^3 P(q)/((1-q)^10(1-2q)^5)`,

where

`P(q)=3-41q+289q^2-1120q^3+2030q^4+474q^5-10207q^6`

`     +22350q^7-25003q^8+15964q^9-5672q^10+984q^11-48q^12`.

For `0<q<=1/128`, bounding just the negative coefficients at `q=1/128` gives `P(q)>5/2`; the positive denominator is at most one. Thus

`kappa_4(q)>=5q^3`, and also `M_4(q)>=5q^3`.                (13)

Now fix one odd centre `y`. There are exactly

`d binomial(d-1,3)`                                       (14)

four-star sets containing `y`: choose their common even hub among the `d` neighbours of `y`, then three other neighbours of that hub. No set is counted twice. Any three distinct neighbours of an even hub have that hub as their only common neighbour: the second common neighbour of the first two is at distance three from the third.

Using `q=1/(Kd)`, (11)--(14) give, separately,

`sum_{four-stars S containing y} |E product_{z in S} g_z|`

`       = d/K^3 + O_K(1)`,

`sum_{four-stars S containing y} |kappa(g_z : z in S)|`

`       = d/K^3 + O_K(1)`.                                (15)

In contrast, the rooted pair sum is exactly

`binomial(d,2) 2q^2/u^2 -> 1/K^2`.

For any desired small upper bound on bad probability, first fix sufficiently large `K`. It stays fixed as `d` grows, so (15) still diverges. Restricting `d` to powers of two does not change this conclusion.

Thus an absolute rooted connected-activity estimate bounded independently of `d`, of the form attempted after (2), is false. Replacing the raw moments by joint cumulants does not remove this particular fourth-order growth. This does **not** preclude a different resummation of all orders or a different global argument.

## 5. The calculation survives ordinary injective sampling

Let `f:E->Omega` now be a uniformly random injection. A four-star involves exactly

`r_0=1+6+4(d-4)=4d-9`

distinct even source variables. Their marginal is a uniform injection of these `r_0` labels, independently of how many additional labels are present in the full injection.

The independent uniform marginal, conditioned to have no repeated host value, is precisely this distribution. The collision probability is at most `binomial(r_0,2)/N`. Thus, for any function `F` of these labels with `|F|<=1`,

`|E_inj F-E_iid F| <= r_0(r_0-1)/N`.                       (16)

Here `|g_y|<=1` since `p<1/16`. So (16) applies to every joint moment needed above. The injective means need not be zero; they must not be dropped in its cumulant. Using the full partition formula

`kappa(g_1,...,g_4)=sum_pi (|pi|-1)!(-1)^(|pi|-1)`

`                         * product_{C in pi} E product_{i in C} g_i`,

the difference of cumulants is at most `75 r_0(r_0-1)/N`. The constant is `sum_pi |pi|! = 1+14+36+24=75`, and follows by telescoping each product of bounded moments.

After summing (14), the errors are `O(d^6/N)`. Our alphabets have `N>=2^(d-1)`, so this error tends to zero. Both asymptotics in (15) therefore hold for uniform **full injections** as well.

This is only a comparison of these fixed four-star statistics. Independent-component factorization in (1) is **not** asserted for injections; their disjoint marginals are not independent. Nor is this a transfer from homomorphism positivity to an injective embedding.

## 6. Scope audit and exact stopping point

These examples do have avoiding injections. Take `s>=m` in the zero-one lift. Send every even source vertex to a different copy index, with one fixed ordinary type and tag `L-1`. The map is injective. Every neighbourhood has tag sum `-d mod L = L-d`, and

`r=wL <= L/(K-1) < L-d`.

The last strict inequality holds for `K>=16,d>=8`, since `L=(Kd-2)^(d-1)` is greater than `2d`. Thus every neighbourhood is good. This check distinguishes a failed proof estimate from an actual packing counterexample.

The all-order attempt stops at the following precise step:

> Equation (2) cannot be extended to a dimension-uniform absolute root-sum estimate for the full centered avoidance expansion on the basis of symmetry and one-coordinate balance alone. Its fourth-order subfamily already violates that estimate by (15), including for actual injection marginals.

To finish by a signed method one would need a genuinely different global treatment of these shared-hub terms, with positivity and original-vertex capacity retained. No such treatment is proved here. The original arbitrary-balanced packing assertion remains open in this work, and no connection converting this diagnostic relation to a red-blue countercolouring has been made. Neither direction of the Lean target is resolved.

## 7. Verification and integrity

`check_cube_balanced_stars.py` checks the balance and lift identities with exact integers/rationals, compares (6)--(9) with direct enumeration of all shared type variables, verifies the polynomial and leading coefficients symbolically, and enumerates the rooted source four-stars in dimensions `5..9`. Its saved output is `CubeBalancedStarExpansionVerification.txt`. These checks audit the displayed all-dimensional paper proofs; they are not a Lean formalization or evidence of a Ramsey resolution.

The unchanged SHA-256 of `Submission/Spec.lean` is

`9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.

## 8. Parent audit: these large rare-hub contributions are positive activities

The obstruction above is specifically to an **absolute** root-sum estimate, not to the negative-activity-only positivity criterion. This distinction is decisive: the exhibited fourth-order moment gives a positive polymer activity, since its support has even size.

More generally, put `a=q/(1-q)>=0`. Formula (6) has the exact graph-cover expansion

`(-1)^t A_t(q) = sum_{F subset E(K_t), V(F)=[t]} a^|F| >= 0`.

Indeed, expand `u^(-binomial(j,2))=(1+a)^binomial(j,2)` into graphs on a selected vertex set `J`, and then sum `(-1)^|J|` over `J` containing the endpoints of each graph. That inner sum vanishes unless every vertex is an endpoint; when it survives it is `(-1)^t`. Thus **all** the conditional rare-hub star contributions have nonnegative signed activity, not only the four-star leading term.

This does not construct a compatible global positive-core decomposition, bound the remaining negative activities, or handle all injections. It prevents misusing Section 4 as a refutation of the existing signed criterion, which deliberately permits arbitrarily large positive activities. No new Ramsey conclusion follows.

## Later update: negative fifth-star obstruction

The positive signs of this report's particular fourth-star and rare-hub
activities remain correct. They no longer leave the analogous raw
negative-only bound untested: `CubeBalancedNegativeStar.md` constructs a
*different* exactly balanced zero-one relation whose negative fifth-star
root load diverges linearly in dimension, even for local injective moments
at a linear-size alphabet. That construction has explicit avoiding
injections and is not a Ramsey counterexample. The signed positivity
criterion remains valid, but balance alone cannot verify its raw
negative-activity hypothesis uniformly. A different resummation or a
stronger graph-specific argument would be required.
