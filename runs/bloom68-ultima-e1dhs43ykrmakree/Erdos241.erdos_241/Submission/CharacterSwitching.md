# Character-dependent switching: a new candidate, not a resolution of Erdős 241

## Status

No unbounded family of strong B3 sets with a fixed cubic excess is established here. Neither the proposed asymptotic nor its negation is proved. `Spec.lean` is unchanged.

The construction investigated here is **not** the image of a Bose set under a fixed quotient. Its character classes are acted on differently, and the resulting points lie in an index-two subgroup. The results below are elementary proofs, not extrapolations from the numerical tests.

## 1. The construction and its actual cyclic modulus

Let q be an odd prime power, let f in F_q[X] be monic irreducible of degree 3, and let theta be a root in K = F_(q^3). Put

    z_t = theta - t                       (t in F_q),
    chi = quadratic character of K*,
    H = (K*)^2,       m = |H| = (q^3 - 1)/2.

Choose a monic irreducible quadratic W for which w = W(theta) has chi(w) = -1. Such a W always exists; see §2. Define

    u_t = z_t       if chi(z_t) = +1,
    u_t = w/z_t     if chi(z_t) = -1.

Every u_t belongs to H. Since H is cyclic, choose a generator h and write u_t = h^(a_t), with 0 <= a_t < m. Thus a B3 subset of these points really does give an integer B3 set {a_t+1} in [1,m]; there is no noncyclic-group embedding loss.

The map t -> u_t is injective. The only potentially new equality is z_a = w/z_b between opposite character classes. It would imply W(theta) = (theta-a)(theta-b). The two monic quadratics have difference of degree at most 1, so W = (X-a)(X-b), contradicting irreducibility.

## 2. Exact number of available quadratic multipliers

Let

    sigma = sum_(t in F_q) chi(theta-t).

Then the number of monic irreducible quadratics W with chi(W(theta)) = -1 is exactly

    (q^2 - 2q + sigma^2)/4.                         (1)

In particular it is positive for every odd q >= 3.

Here is an elementary proof, avoiding an unproved character-sum estimate. Write

    f(X) = X^3 + c2 X^2 + c1 X + c0.

For y = A + B theta + C theta^2, the theta^2 coefficient of y^2 is

    B^2 + 2AC - 2c2 BC + (c2^2-c1) C^2
      = (B-c2 C)^2 + 2(A-c1 C/2)C.

Consequently exactly q(q-1)+2q = q^2+q elements y have theta^2 coefficient of y^2 equal to 1. The monic quadratics W evaluate bijectively to the elements with theta^2 coefficient 1, none of which is zero. Counting square roots therefore gives

    sum_(W monic, deg W=2) chi(W(theta)) = q.

The sum over reducible monic quadratics is

    sum_(a<=b) chi(z_a)chi(z_b) = (sigma^2+q)/2,

where the notation just means unordered pairs, including repeated roots. There are q(q-1)/2 irreducible monic quadratics. Subtracting the reducible contribution and separating signs gives (1).

## 3. What is proved: all q switched points are B2

First recall the ordinary Bose argument, with multiplicities: equality of two products of three z_t gives two monic cubics whose difference has degree at most 2 and vanishes at theta. The polynomials, and therefore their root multisets, are equal. The same holds for products of at most three factors.

For products of switched points, call r the number of factors from the negative character class. Two products of the same length <=3 and the same r are equal only for identical multisets. Cancel w^r and move inverse factors to the opposite side. This gives an equality between products of at most three original z_t. Their positive and negative parameter classes are disjoint, so the Bose multiset equality recovers the original switched multisets.

For B2 it remains to compare pairs with different r.

* If the counts differ by 1, equality implies P_3(theta) = W(theta)Q_1(theta), where P_3 and Q_1 are monic and split over F_q. Both polynomials P_3 and W Q_1 are monic of degree 3. Their difference has degree at most 2, so P_3 = W Q_1. This is impossible because W is irreducible of degree 2.

* If the counts differ by 2, equality implies P_4(theta)=W(theta)^2, with two roots of P_4 from each character class, including multiplicity. Monicity gives

      P_4 - W^2 = k f

  for a scalar k. We have k != 0 because P_4 splits and W does not. For every root t of P_4,

      -f(t) = W(t)^2/k.

  But Norm_(K/F_q)(theta-t) = -f(t), and chi_K(z) = chi_q(Norm z). Hence every root of P_4 has chi_K(theta-t)=chi_q(k), contradicting the two different classes.

This proves the full repeated-summand B2 property. It does **not** prove B3.

## 4. Exact remaining B3 equations, including repeated summands

Let S be any subset of F_q. A nontrivial triple collision among {u_t : t in S} exists if and only if the following data exist:

* d in {1,2,3} and r in {0,...,3-d};
* monic polynomials P,Q, split over S with multiplicities, of degrees 3+d and 3-d;
* P has exactly r+d negative-character roots and 3-r positive-character roots;
* Q has exactly r negative-character roots and 3-r-d positive-character roots;
* a nonzero polynomial R of degree at most d-1 such that

      P - W^d Q = f R.                              (2)

For d=3, Q=1.

Proof: orient a collision so that the two triples have negative counts r and r+d. Moving all inverse factors across gives P(theta)=w^d Q(theta), with exactly the root counts displayed above. Both P and W^d Q are monic of degree 3+d, so their difference has degree at most 2+d. Divisibility by f gives (2). Conversely, (2) evaluated at theta reconstructs two triples of switched points of cardinality 3 and different negative counts. They are distinct. This is an equivalence, not merely a necessary condition. Products and root counts throughout are multisets, so repetitions are included.

Since the whole switched set is B2, two distinct colliding triples cannot share a parameter: cancelling it would give a B2 collision. Consequently P and Q in any actual obstruction are coprime. Repetitions within either triple remain allowed.

Thus the new avoidance problem has degrees (4,2), (5,1), and (6,0), with multipliers W, W^2, and W^3. It is different from the fixed-quotient equation P_3 - lambda Q_3 = (1-lambda)f.

## 5. A concrete repeated-summand failure

Over F_5, take

    f = X^3 + 3X + 3,          W = X^2 + X + 1.

Both are irreducible, and Norm(W(theta))=3 is a nonsquare. The parameters 0,1,2 are in the negative class and 3,4 are in the positive class. There is the exact polynomial identity

    (X-4)(X-1)^2(X-2) - (X^2+X+1)X^2 = f.          (3)

It gives the switched triple collision

    u_0^2 u_4 = u_1^2 u_2.

For a root theta of f, theta is primitive of order 124. With h=theta^2, the parameter-ordered exponents are

    [23, 34, 26, 38, 48] in Z/62Z.

In fact the integer equality is already

    23+23+48 = 34+34+26 = 94.

Identity (3) and its character pattern persist over F_(5^e) when gcd(e,6)=1. In particular, that fixed f,W choice fails cyclic B3 for an unbounded sequence of q. This does not establish a uniform obstruction for arbitrary choices of f,W or arbitrary deletions, nor does cyclic failure alone exclude every possible integer lifting.

## 6. Precise asymptotic gap

To obtain the requested disproof by this construction, it would suffice to find an unbounded sequence of q, suitable f,W, and subsets S satisfying (2)-avoidance and

    |S| >= rho q,       rho > 2^(-1/3) = 0.7937005259...

Then the integer sets in §1 would satisfy, with N=(q^3-1)/2,

    |A|^3/N >= 2 rho^3 q^3/(q^3-1) > 2 rho^3 > 1.

For example, retaining 4/5 of the parameters would give the fixed excess c=128/125. No such retention theorem or family has been obtained. Taking only one character class is automatically B3, but its size is (q +/- sigma)/2. The Hasse bound on the elliptic curve y^2=-f(x) gives |sigma| <= 2 sqrt(q), so a single class does not reach the required density asymptotically.

## 7. Integer-only reflection was also considered

A cyclic collision was not assumed to imply an integer collision. For Bose logarithms B in [0,M), M=q^3-1, set m=M/2 and

    U = {b/2 : b in B, b even},
    V = {(M-1-b)/2 : b in B, b odd}.

For any integer t, consider U union (V+t). All triple sums with a fixed number r of V-elements are automatically distinct, by the same multiset argument as above. If C_r is the set of their unshifted sums, the exact remaining criterion is

    C_i intersect (C_j+(j-i)t) = empty   for 0 <= i < j <= 3.

This criterion also detects coinciding points by padding to triples. The interval length is exactly

    max(max U,max V+t) - min(min U,min V+t) + 1

when both classes are nonempty. A bounded relative translation could in principle improve the interval constant even without a cyclic B3 set.

For a full q-point set, an interval of length at most M=q^3-1 is possible only for the translations in the exact range

    max U - min V + 1 - M <= t <= M - 1 + min U - max V.

The attached exact modular-NTT audit exhausts this entire range. For the specified bases in `integer_reflection_bases.json`, it finds no valid translation at q=17,19,23,31,41,61,101. Small q do have finite excess: the best interval lengths in this model at q=5,7,11,13 are respectively 60,146,996,1949. Each returned set was checked by direct enumeration of all repeated triples.

These are finite statements for the supplied bases, not a claim about all Bose bases, all choices of logarithm generator, all deletions, or an asymptotic nonexistence theorem. In particular the finite excesses are not a disproof of the proposed asymptotic.

## 8. Verification files

* `character_switching.py`: enumerates odd character-switch shifts on specified Bose/Singer bases and checks all repeated triples.
* `quadratic_switching_audit.py`: verifies (1), the B2 property, and polynomial certificates (2), for the stated finite fields; writes a compact JSON report.
* `integer_reflection_audit.cpp`: exact modular-NTT audit of the translation criterion in §7. Nonzero convolution coefficients certify actual integer equalities; no floating-point zero test is used in the reported exclusion scan.

None of these finite computations is offered as an unbounded fixed-excess family or as a proof of the original asymptotic.
