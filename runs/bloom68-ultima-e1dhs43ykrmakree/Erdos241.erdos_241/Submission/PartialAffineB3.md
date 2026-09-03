# Partial binary affine flats: exact constraints and a scoped uniform obstruction

## Status

**The unrestricted critical-dimension problem is not resolved.** This note does not construct an unbounded strong cyclic B3 family with fixed cubic excess, and does not rule out arbitrary dense subsets of arbitrary binary affine k-flats in F_(2^(3k-1)). It is not a proof or disproof of the assertion in `Spec.lean`.

What is established here is:

1. Exact partial-flower loads, with all m affine centers retained in the bookkeeping, including centers outside the selected subset.
2. A deletion-robust version of the actual field identity involving `ab = uv`, rather than a rank/trace relaxation.
3. A uniform obstruction for **scaled-Frobenius-stable** affine flats: every strong B3 subset has density at most `2/3 + O(1/m)`. There is an explicit infinite sequence of such flats at the exact critical dimensions `n=3k-1`; almost all their points have full field degree n, so this example is not merely confinement to a smaller subfield.
4. An infinite Bose family showing that the full-flat reciprocal nonvanishing condition is **not deletion-stable, even for strong B3 subsets of density tending to one**. Two deletions suffice to make the reciprocal sum zero. This family is at `n=3k`, not `3k-1`, and its cubic ratio tends to one from below.

All B3 assertions below concern multisets, including repeated factors. No scalar-extension amplification claim is made. `Spec.lean`, `Reductions.lean`, and `SignedSums.lean` are unchanged. The accompanying audit is mathematical-computational verification, not a Lean formalization.

## 1. Notation and the exact target

Let K be a finite field of characteristic two, `Q=|K|`, and let

    A = a + U,       dim_F2 U = k,       a notin U,
    m = |A| = 2^k,   S subset A,         N = |S|,
    D = A \ S,      d = |D| = m-N.

Thus A and S contain no zero. Call S multiplicatively strong B3 if equality of two products of three elements of S implies equality of their factor multisets. Taking discrete logarithms in the cyclic group K* gives exactly a strong cyclic B3 set modulo `M=Q-1`.

At the critical dimension `n=3k-1`, `Q=m^3/2`. Writing `rho=N/m`, the cubic ratio is

    N^3/(Q-1) = 2 rho^3 / (1-2/m^3).

An asymptotic retention constant exceeding `2^(-1/3)` would therefore give the requested fixed excess.

## 2. Exact partial flowers

For `u in U`, let r(u) count unordered multiset pairs from S with additive sum u. Then

    r(0) = N,
    r(u) = |S intersect (S+u)|/2       if u != 0.           (1)

For **every** center `z in A` and every `c in S`, define the reduced petal

    T_(z,c) = { xy/c : x,y in S, x+y=z+c, c notin {x,y} }.

The full ambient petal is the one in the question. Indeed, with

    u=z+c,       v=x+c in U,       L_u(v)=v^2+uv,

one has

    xy/c = z + L_u(v)/c.                                  (2)

For fixed u, an unordered pair is determined by its sum and product, so there are no internal multiplicities in a single petal, even without assuming B2. Exactly one pair has c as a factor when `z in S`, namely `{c,z}`. Consequently

    |T_(z,c)| = r(z+c) - 1_S(z).                          (3)

Also `z notin T_(z,c)`: a pair with sum `z+c` and product `zc` would be exactly `{z,c}`, which was excluded.

Define a flower as a labeled collection of its reduced petals, together with the point z if `z in S`. Its **required load**, before allowing collisions between different petals, is

    h(z) = sum_(c in S) r(z+c) - (N-1) 1_S(z)
         = (1/2) (1_S * 1_S * 1_S)(z)
             - (N/2-1) 1_S(z).                           (4)

Convolution here is additive counting convolution in K. In particular, the centers are all m points of A, not just the N points of S.

### Exact packing criterion

S is strong B3 if and only if the reduced petals are disjoint within each flower and the resulting flowers at distinct centers are disjoint.

To justify the converse without silently assuming B2, first use the equivalent signed formulation: the values `xy/c`, with `{x,y}` an unordered multiset pair from `S\{c}`, must be mutually distinct and disjoint from S. A nontrivial B2 equality has disjoint pair supports, and would put such a reduced signed value in S. Thus this formulation implies B2. A nontrivial triple equality can then have no factor in common across its two sides; transferring one factor from each side gives two distinct reduced signed representations of the same value. This proves B3. Conversely, B3 directly gives signed uniqueness and disjointness from S. Formula (2) assigns each representation one center, and a reduced petal never contains its own center, proving the flower criterion.

This argument includes repeated positive factors throughout.

### Deletion formula

For `z in A`, let

    e_D(z) = #{(d1,d2,d3) in D^3 : d1+d2+d3=z}.

Expanding `1_S=1_A-1_D` in additive counting convolution gives the exact identity

    (1_S * 1_S * 1_S)(z)
        = m^2 - 3md + 3d^2 - e_D(z).                     (5)

Since `0 <= e_D(z) <= d^2`, this gives uniform load bounds through (4), in particular

    N(2N-m) <= (1_S * 1_S * 1_S)(z)
             <= m^2-3md+3d^2.                           (6)

The lower bound can of course be negative at low retention and is then harmless. Summing (4) gives

    sum_(z in A) h(z) = N + N binom(N,2)
                     = (N^3-N^2+2N)/2.                 (7)

If S is B3 this is the actual occupied cardinality in K*. At `Q=m^3/2`, the exact number of holes **in K, including zero**, is therefore

    H = (m^3-N^3+N^2-2N)/2.                             (8)

For the full flat this reduces to `m(m-2)/2`. But at retention rho,

    H/Q = 1-rho^3 + rho^2/m - 2rho/m^2.                 (9)

Thus retention 4/5 leaves asymptotically **48.8% of K as holes**. The full-flat almost-packing is not an almost-packing at the excess threshold: when rho approaches `2^(-1/3)`, the occupied fraction approaches one half, not one. An obstruction that only forces `O(m^2)` extra full-flat defects would not by itself settle fixed retention near 0.8.

## 3. A deletion-robust actual reciprocal constraint

For `w != 0`, put

    R_w = {u in U\{0} : w/u in U\{0}},
    epsilon_w = 1 if sqrt(w) in U, and 0 otherwise.

These are actual field inverses, not variables in a rank model.

### Proposition

If S is strong B3, then for every two distinct `a,b in S`, writing `t=a+b`,

    |R_(ab)| + epsilon_(ab)
        <= 4d - 2 |D intersect (D+t)|.                  (10)

In particular, the full-flat conclusion `ab notin U*U` is recovered when d=0.

### Proof

Let

    B = (D+a) union (D+b) subset U,
    T = U\B = (S+a) intersect (S+b).

Then

    |B| = 2d - |D intersect (D+t)|.

Suppose `u,v in T` and `uv=ab`. All six factors in

    a(b+u)(b+v) = b(a+u)(a+v)                           (11)

belong to S. Expanding the difference of the two sides gives `(a+b)(ab+uv)=0`, so (11) is an equality. It is nontrivial: a occurs on the left and does not occur on the right, because `a != b` and `u,v != 0`. This also handles `u=v`, when the collision has repeated factors.

Consequently, every orbit of the involution `u -> ab/u` on `R_(ab)` meets B. Its only possible fixed point is `sqrt(ab)`, and that point must itself be in B if it belongs to U. Counting two-element orbits and the possible fixed point yields

    |R_(ab)| + epsilon_(ab) <= 2 |B intersect R_(ab)| <= 2|B|,

which is (10).

### Scope of this constraint

For example, if a selected pair has `|R_(ab)|+epsilon_(ab)` close to m, (10) forces roughly one quarter of the flat to be deleted. It is a genuine partial-flat obstruction, but no lower bound of this size for a selected pair is established for arbitrary critical flats. It must not be substituted for such a lower bound.

## 4. A uniform obstruction for scaled-Frobenius-stable flats

For `c in K*`, define the permutation

    F_c(x) = x^2/c       on K*.

It has exactly one fixed point, namely c.

### Theorem

Suppose a finite set A in K* satisfies `F_c(A)=A`. Every strong B3 subset S of A satisfies

    |S| <= floor((2|A| + 1_(c in A))/3).                 (12)

This applies in particular to arbitrary partial subsets of a binary affine flat invariant under scaled squaring. At `n=3k-1`, it gives

    limsup |S|^3/(2^(3k-1)-1) <= 16/27 < 1.             (13)

Indeed, the bound is already below one at every critical m>=4 when using `(2m+1)/3` as the cardinality upper bound.

### Proof

For every x,

    F_c(x)^3 = x^2 F_c^2(x).                            (14)

If `x != c`, the triples `{F_c(x),F_c(x),F_c(x)}` and `{x,x,F_c^2(x)}` are distinct. Thus S cannot contain all three consecutive orbit points. This remains valid for a two-cycle: then the collision is between two tripled elements.

On each nontrivial cycle, every cyclic window of length three has at most two selected occurrences. Summing these inequalities counts each selected point three times and gives at most two thirds of the cycle, rounded down. A fixed point may be retained. This proves (12). Substituting `Q=m^3/2` proves (13).

For a cycle of length L>=3, the sharper individual upper bound is `floor(2L/3)`. This is only an upper bound for B3 subsets; a pattern attaining the orbit bound need not be B3 for other reasons.

### Exact affine criterion and the actual reciprocal sum

For `A=a+U`, scaled-Frobenius invariance is equivalent to

    U^2 = c U,       a^2/c+a in U.                      (15)

Write the subspace polynomial as

    P_U(X) = X^m + sum_(i<k) u_i X^(2^i),
    beta = P_U(a) != 0,       u_0 != 0.

The actual reciprocal identity is

    R_A := sum_(x in A) 1/x = u_0/beta != 0.             (16)

If `F_c(A)=A`, summing reciprocals after applying F_c gives

    R_A = c R_A^2,

so the **only possible** c is

    c = R_A^(-1) = beta/u_0.                            (17)

Equivalently, for this candidate c, the monic root polynomial

    c^(-m) [P_U(cX)+beta]

has all coefficients in F2. Indeed, its root set is A/c, and a finite root set in K is stable under squaring exactly when its monic root polynomial is Frobenius-fixed.

This provides an exact certificate that can be tested by subspace arithmetic without enumerating triples. It does not show that an arbitrary flat passes the certificate.

There is also an exact description of this class after scaling by c. Its members are precisely the nonempty root sets

    {x in F_(2^n) : p(F)(x)=1},

where p is a monic degree-k divisor of `T^n-1` and `(T^n-1)/p` vanishes at T=1. Here `F(x)=x^2`. The kernel dimension and image assertions are proved in (19) below. Conversely, the normalized root polynomial of any stable affine flat has coefficients in F2 and nonzero constant and linear coefficients both equal to one. If its linearized part is p(F), then `ker p(F)=ker gcd(p,T^n-1)(F)` by Bezout; the kernel dimension forces p to divide `T^n-1`. Solvability of the affine equation gives the condition on the complementary factor.

## 5. Explicit infinite critical flats to which the obstruction applies

The following construction shows that Section 4 applies to a genuinely infinite exact-critical family, not just to a finite list or to flats wholly inside proper subfields.

For each integer `j>=1`, put

    ell = 4^j,
    n = 5 ell,
    k = (5 ell+1)/3,
    t = (ell+2)/6,
    Phi(T) = T^4+T^3+T^2+T+1,
    p(T) = (T+1)^(ell-1) Phi(T)^t.

All these exponents are integers, and `n=3k-1`. Work in `K=F_(2^n)`, let `F(x)=x^2`, and define

    A_j = {x in K : p(F)(x)=1}.                         (18)

Here `p(F)` is the linearized operator `sum p_i x^(2^i)`, not ordinary evaluation of p at x.

### Proposition

A_j is a nonzero affine binary k-flat, stable under squaring. Moreover,

* exactly `2^(ell-1)` of its points have field degree ell;
* all its other `2^k-2^(ell-1)` points have full field degree n.

In particular, A_j is not contained in any proper subfield. Nevertheless every strong B3 partial subset has density at most 2/3, and cannot produce the requested cubic excess.

### Proof of existence and dimension

Since

    T^n-1 = (T^5-1)^ell = (T+1)^ell Phi(T)^ell,

p divides `T^n-1`, and

    deg p = ell-1+4t = (5ell+1)/3 = k.

We use an elementary linearized-polynomial fact. If p divides `T^n-1` and q is the quotient, then

    dim ker p(F) = deg p,       im p(F) = ker q(F).       (19)

The root bound for the nonzero linearized polynomial p(F) gives `dim ker p(F)<=deg p`. The containment `im q(F) subset ker p(F)` and the analogous bound for q give the reverse inequality. Interchanging p and q gives the image statement.

Here the complementary factor is `(T+1) Phi(T)^(ell-t)`, which vanishes at T=1. Thus `1 in im p(F)`, by (19). Equation (18) has an affine solution space of dimension k and excludes zero. Also F commutes with p(F) and fixes 1, so A_j is Frobenius-stable. The point 1 is not in A_j, since p(1)=0. Thus (12) applies without a fixed-point correction.

### Proof of the field-degree assertion

First, `A_j intersect F_(2^(n/2))` is empty. On that subfield, the operator

    Phi(F)^(ell/2) p(F)

is zero, because its polynomial is divisible by

    T^(n/2)-1 = (T+1)^(ell/2) Phi(T)^(ell/2).

But applying it to a putative equation `p(F)x=1` gives `0=Phi(1)^(ell/2)=1`, a contradiction.

On `F_(2^ell)`, the operator Phi(F) is invertible, since Phi is coprime to `(T+1)^ell`. Hence (18) has exactly `2^(ell-1)` solutions there: after the invertible change of variable it is `(F+1)^(ell-1)y=1`, whose kernel has dimension ell-1 and whose image is F2. These solutions have full degree ell, since any proper subfield of `F_(2^ell)` lies in `F_(2^(n/2))`.

The only maximal proper subfields of K have degrees ell and n/2. Thus every remaining point has degree n, proving the claim. Nor can A_j lie in a scalar multiple of a proper subfield: if `A_j subset lambda L`, then `x,x^2 in A_j` would imply `x=x^2/x in L` for every x in A_j. Thus the obstruction here is not just an elementary count inside a smaller multiplicative subfield group.

In particular, the exact Frobenius cycle counts in A_j are

    2^(ell-1)/ell                    cycles of length ell,
    (2^k-2^(ell-1))/(5ell)            cycles of length 5ell.

These give a slightly sharper integer bound by summing `floor(2L/3)` cycle by cycle. At j=1, `(n,k)=(20,7)`, there are two 4-cycles and six 20-cycles, so every strong B3 subset has at most `2*2+6*13=82` of the 128 points. No claim is made that 82 is attainable.

## 6. Two deletions can erase the reciprocal constraint uniformly

The nonzero reciprocal sum of a full affine flat cannot simply be imposed on its dense B3 subsets.

### Theorem

For every `e=3r+1` with `r>=1`, put `q=2^e` and take

    K=F_(q^3),       theta in F_8\F_2,
    A_q = theta + F_q,
    S_q = theta + (F_q\{0,1}).                          (20)

Then S_q is strong multiplicative B3, has `q-2` points in an affine binary e-flat, and

    sum_(x in S_q) 1/x = 0.                             (21)

Its relative density tends to one.

### Proof

Because `gcd(e,3)=1`, theta has degree three over F_q. Equality of two products of three factors `theta+t`, including repetitions, gives two monic split cubic polynomials whose difference has degree at most two and vanishes at theta. Their difference is zero, so their root multisets agree. Thus the entire A_q is strong B3.

Since `e=1 mod 3`, `theta^q=theta^2`. The full subspace-polynomial identity gives

    sum_(t in F_q) 1/(theta+t)
       = 1/(theta^q+theta)
       = 1/(theta^2+theta)
       = 1/theta + 1/(theta+1).

Deleting the two displayed points proves (21). Strong B3 is inherited by S_q.

### Important normalization

This is at binary field dimension **3e**, not `3e-1`. Its cyclic order is `q^3-1`, and

    |S_q|^3/(q^3-1) = (q-2)^3/(q^3-1) < 1,

with limit one. It is not the requested fixed-excess family. Its role is to show, by an actual infinite strong B3 construction rather than a relaxed model, that reciprocal nonvanishing alone is not a robust dense-subset obstruction.

## 7. Verification and remaining gap

`partial_affine_b3_audit.sage` checks:

* the partial-flower criterion and load formulas on all subsets of several selected small flats, including examples that are not B2;
* the actual inverse-orbit deletion inequality (10) for the B3 subsets in that audit;
* the invariant-flat linear algebra at `(n,k)=(20,7)` and `(80,27)`, including the two maximal-subfield intersection assertions;
* all Frobenius cycles of the 128-point example and the resulting upper bound 82;
* the reciprocal-cancellation construction at q=16 and q=128, with direct enumeration of repeated triple products.

The finite audits are checks of the stated uniform proofs, not an extrapolation from the absence of full flats. They do not purport to search every critical partial flat.

The missing step remains substantial. For arbitrary A at `n=3k-1`, neither scaled-Frobenius stability nor a large actual reciprocal intersection `R_(ab)` has been proved. Section 2 gives exact constraints for the remaining flats, but no incidence/covering defect large enough to force retention below `2^(-1/3)`. Consequently **neither an unrestricted uniform partial-flat obstruction nor an unbounded fixed-excess family is established here**.
