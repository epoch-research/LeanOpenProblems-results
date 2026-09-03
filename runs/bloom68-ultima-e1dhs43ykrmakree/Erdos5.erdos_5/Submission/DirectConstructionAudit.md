# Direct-construction continuation: checked results and unresolved step

## Status

No proof or disproof of Erdős #5 was obtained. `Submission/Spec.lean` has not
been edited, and neither of its unproved declarations was used. The results
below concern attempted constructions, not counterexamples to the conjecture.
Both independent investigations returned; no agent is still running.

## 1. Complementary-factor Euclid differences

Let Q_y be the product of all primes at most y. If Q_y divides M=AB,
(A,B)=1, and 1<|A-B|<=y^2, then |A-B| is prime. Indeed, a composite
difference would have a prime divisor p<=y. Such a p divides AB and the
difference, hence both A and B, contradicting coprimality.

This suggests taking a huge seed M and cancelling its two factors to obtain
prime outputs near X, while taking y>=sqrt(2X). However, different outputs
of the same seed are too widely spaced in the certified range.

For two ordered factor pairs with product M, put e_i=B_i-A_i and s_i=A_i+B_i.
Then s_i^2=4M+e_i^2. If e_1<e_2, the integer s_2 is at least s_1+1, so

    e_2^2 >= e_1^2 + 2s_1 + 1.

In particular, if both differences are at most y^2 and y^8<=16M, they are
equal. Since log Q_y~y, the inequality y^8<=16M holds eventually whenever
Q_y divides M. Thus there is at most one distinct output in the entire
range where this roughness-and-size argument certifies primality.

The corresponding real-number spacing bound is

    e_2^2-e_1^2 > 4 sqrt(M).

If X<=e_1<e_2<=2X and H=e_2-e_1, it implies M<X^2 H^2. Consequently a
logarithmic gap H=O(log X) requires log M<=2log X+2loglog X+O(1), whereas
Q_y|M and y>=sqrt(X) require log M>=(1+o(1))sqrt(X).

### A known endpoint does not fix the height

For a prime p, take y=sqrt(2p), Q=Q_y and M=Q(Q+p). The coprime factors
Q,Q+p yield output p. For large p, Q>p^2. Every different output d obeys

    d^2 >= p^2+4Q+2p+1.

There are no smaller positive outputs: that would force the square of the
sum to fall by at least 4Q+2p-1>p^2. All other outputs therefore exceed 2p.
Bertrand's theorem supplies an actual prime strictly between p and 2p,
so any larger prime output is not globally consecutive to p.

This is specifically a fixed-product obstruction. It does not rule out
varying products or other primality certificates.

### Lean verification

`Submission/DirectConstructionAudit.lean` has seven completed elementary
lemmas, including the primality certificate, square spacing, and uniqueness
under y^8<=16M. It imports only `FormalConjecturesUtil`, not Spec. The main
assistant read the file, compiled it independently, and checked all seven
axiom reports: only `propext`, `Classical.choice`, `Quot.sound` occur. There
are no `sorry` proofs or new axioms. No prime-gap existence result is asserted.

## 2. Different multiplicative orders on the two endpoints

The efficient K=2 construction in `SparseExistenceAudit.md` provides an
interval with endpoints N,N+d and a residue class a modulo Q, where

    d=C log X+o(log X),  Q=X^o(1),  gcd(a(a+d),Q)=1.

All integers strictly between the endpoints are composite on the selected
rows N in [X,2X]. This does not assume either endpoint prime.

Put L=log X and Z=Q L^6. Choose distinct primes Z<r<2Z and 2Z<s<4Z, and add

    N=1 mod r,   N+d=1 mod s.

For sufficiently large X, r,s>d+1 and r,s do not divide Q. CRT gives one
class modulo Qrs. Both endpoint classes are reduced. Let A be its rows in
[X,2X], with T=|A|=X/(Qrs)+O(1)=X^(1-o(1)).

Define B_L to contain rows where N=(1+ru)(1+rv) with u,v>=1, and B_R
similarly using N+d and s. The following simultaneous screening estimate
is unconditional and was independently checked:

    |B_L union B_R| << X log X/Z^3 + sqrt(X)/Z,
    |B_L union B_R|/T << L^(-5)+X^(-1/2+o(1)).

For B_L, order u<=v. Then u<=sqrt(3X)/r and v<=3X/(r^2 u). The congruence
(1+ru)(1+rv)=1-d mod s either has no solutions in v or fixes one residue
class modulo s; its right side is nonzero. Summing
3X/(r^2 s u)+1 over u proves the bound. Interchanging r,s proves the other
half. Ignoring the Q-congruence is legitimate for this upper bound, and
its resulting loss is explicitly included in the ratio Q log X/Z.

For a prime order r, let E_r(m) mean that a nonidentity r-th root of unity
exists modulo m. Equivalently r divides phi(m). On the good rows
G=A minus (B_L union B_R),

    E_r(N) iff N is prime,
    E_s(N+d) iff N+d is prime.

For the nontrivial direction, N=1 mod r implies r does not divide N. If
r divides phi(N), some prime ell|N satisfies ell=1 mod r. If N is composite,
its complementary factor is also 1 mod r and both factors exceed 1, putting
N in B_L. The converse for a prime is Fermat/Cauchy in its unit group.

Thus, if P_A denotes the prime-pair count on A,

    0 <= sum_A 1_{E_r(N)} 1_{E_s(N+d)} - P_A <= |B_L union B_R|.

The established advance in this attempted construction is the negligible
composite false-positive bound with a subpower CRT cost. There is still
NO lower bound for the joint order-event sum. For example,

    sum_A 1_{E_r(N)} 1_{E_s(N+d)} >= T/(log X)^4

on unbounded scales would suffice, but has not been proved. On G these
events are exactly simultaneous primality; merely constructing T rows
does not construct any order witnesses. Inserting a proper prime factor
ell=1 mod r to manufacture a witness puts the row in the discarded set.

### Fixed polynomial witness formulas cannot supply the missing event

Fix N(t)=Mt+a, gcd(M,a)=1, an odd prime r, and U in Z[t] of degree k. Put
R=M^k U(-a/M), an integer. Since Mt=-a mod N(t),

    M^k U(t)=R mod N(t).

A proposed witness U(t)^r=1 mod N(t) therefore gives

    N(t) divides R^r-M^(kr).

If this fixed integer is nonzero, there are only finitely many positive
N(t). If it is zero, oddness gives R=M^k, and invertibility of M modulo
N(t) makes U(t)=1 mod N(t), the trivial root. This rules out fixed
polynomial witness formulas on a fixed linear progression, not changing
formulas/orders with scale.

Also, if irreducible F in Q[t] divides U^r-1 but not U-1, the field Q[t]/F
contains a primitive r-th root, so r-1 divides deg F. The full cyclotomic
value Phi_r(u), u>=2, is at least 2^(r-1), far above X for the orders chosen
here. Selecting smaller proper factors again needs additional arithmetic.

The standard order-certificate implication was cross-checked against
`/corpus/src/1011.4836/grau-oller-proth-revisado3.tex`, lines 56-74 and
126-139. That source gives primality certificates, not simultaneous
witness existence. The screening calculation and polynomial obstruction
above were derived directly, not attributed to that source.

## 3. Exact task remains unresolved

If simultaneous endpoint primes were obtained at these rows, the already
covered middle would make them globally consecutive. For the global
zero-based prime index j, PNT gives log j=log p-loglog p+o(1), so the intended
d/log j limit would indeed be C. No such pair construction was completed.

Spec SHA-256 remains

    47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123

Both original `sorry` proofs remain. Neither proof claim can be submitted.
