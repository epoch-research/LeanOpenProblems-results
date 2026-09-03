# Growing binary digit moments: polynomial-length obstruction

The square-Sidon conjecture is not settled. No actual Sidon exponent improvement
or fixed-power upper bound was obtained. The main file has not been changed.

## Verified results

Three clean auxiliary modules implement this continuation:

* `SmallSignJets.lean` imports only `FormalConjecturesUtil`.
* `SignedBlockMoments.lean` imports the clean `MomentLifting.lean` module.
* `GrowingMomentObstacle.lean` combines the preceding two modules.

All printed axiom audits contain only propext, Classical.choice, Quot.sound.
None of these three modules contains an admission.

### 1. Bounded-sign polynomials with many vanishing moments

`Erdos773.SmallSignJets.exists_signed_jet_of_count` proves that if

    (D^k + 1)^k < 2^D,

there is a nonzero polynomial V in Z[X], degree <D, leading coefficient 1,
every coefficient in {-1,0,1}, and (X-1)^k dividing V.

Proof: color binary words of length D by the first k Taylor coefficients at
one. Each coefficient is a sum of binomial coefficients bounded by D^k.
Two words have the same color; their difference is the desired polynomial,
up to changing its sign.

The explicit corollaries for k>=1 are:

* `exists_signed_jet_cubic`: degree <16*k^3.
* `exists_signed_jet_quadratic_log`: degree <16*k^2*(k.log2+1).

For the latter bound put ell=k.log2+1 and D=16*k^2*ell. Then D<=2^(7ell),
and the number of colors is at most D^(2k^2)<=2^(14*k^2*ell)<2^D.

### 2. Signed-block multiplication

`Erdos773.SignedBlockMoments.collision_from_signed_polynomial` converts a
polynomial V as above, of degree d, into binary words P,Q,R,S of length
4*(d+1). Their evaluations at two are

    (3M, 11M, 7M, 9M),    M=V(16)>0.

Thus their squares collide nontrivially, and the roots satisfy the strict
order 0<P(2)<R(2)<S(2)<Q(2).

The important carry fact is that multiplication by V(2^L) can be encoded
using signed blocks. At a negative block a borrow replaces an odd input
word by its complement, with a correction independent of the input word.
At a zero block an existing borrow produces an all-one block. The proof
tracks this borrow explicitly, proves all coefficients remain binary, and
proves the evaluation identity by telescoping.

For any two odd input words p,q, their encoded polynomial difference is

    V(X^L)*(p-q).

Since (X-1)^k divides V, it also divides V(X^L). The first k positional
binary digit moments of all four encoded words therefore agree.

### 3. Quantitative collision theorems

In namespace `Erdos773.GrowingMomentObstacle`:

* `matching_moment_collision_cubic` gives length

      4*(k+1) <= L <= 64*k^3.

* `matching_moment_collision_quadratic_log` improves this to

      4*(k+1) <= L <= 64*k^2*(k.log2+1).

Both provide binary words with bounded support, positive pairwise distinct
evaluated roots, the square-sum identity, agreement of moments j<k, and an
explicit negation of the Sidon property of the four square values.

The length bound shows that the older exponential-length moment lifting
was not a lower bound on possible counterexample length. In particular,
for any fixed positive constants C,r, taking k sufficiently large makes
these examples agree in at least C*(log L)^r moments. This last asymptotic
rephrasing is an explanatory consequence of the proved quantitative bound,
not a separately formalized Lean theorem.

## Scope and cautions

* This refutes a blanket sufficient criterion, NOT Erdos 773.
* It does not show that every moment class fails, or rule out choosing a
  special class and then deleting a small exceptional subset.
* These collisions are common multiples of (3,11,7,9). Do NOT claim their
  roots are primitive, pairwise coprime, or prime. In particular, the new
  result is not a growing-moment extension of the earlier primitive
  three-moment example.
* Efficient high-vanishing signed polynomials may vanish at additional roots
  of unity. This can impose small common factors on their evaluated
  multipliers; it must not be ignored in a proposed primitive extension.
* No positive higher-digit modular Sidon lift with subpower loss was obtained.

Logs:

    /tmp/small-sign-jets.log
    /tmp/signed-block-moments.log
    /tmp/growing-moment-obstacle.log
    /tmp/spec-growing-moment-check.log

`Spec.lean` still has its sole admission at line 2031, for 0<epsilon<=1/3.
No proof submission has been made.
