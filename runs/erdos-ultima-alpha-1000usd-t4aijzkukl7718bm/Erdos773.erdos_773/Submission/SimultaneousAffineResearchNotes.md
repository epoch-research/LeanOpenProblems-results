# Simultaneous affine squares: bounded capacity and a capacity-one obstruction

This is NOT a settlement of Erdős 773. The unchanged Spec.lean still has its
sole admission for 0 < epsilon <= 1/3. No proof submission has been made.

## Verified simultaneous selection

Files:

* SimultaneousDifferenceSelection.lean
* SimultaneousAffineSquares.lean

The generic finite selection theorem takes a finite family J of injective
maps f_j : Fin N -> Nat, with values at most R, and an upper bound K on the
number of oriented representations of every positive difference. For any
0 <= p <= 1 and capacity g, it supplies one B with all these capacities at
most g and

  |B| >= p N - |J| R K^(g+1) p^(g+2).

The support of g+1 equal positive differences has at least g+2 vertices:
second endpoints are distinct, and the least first endpoint is not one of
them. Bernoulli alteration removes the supports. The public finite theorem
requires only injectivity; the affine-square specialization is strictly
increasing, so the index orientation includes all positive differences.

The normalized quadratic is

  quadratic(q,r,n) = q n^2 + 2 r n.

Its positive-difference representations inject into the divisors of D via

  D = (b-a)(q(a+b)+2r).

For every fixed k and epsilon>0 there is a fixed g such that, eventually in
N, ONE actual root set A subset [1,N], |A| >= N^(1-epsilon), has at most g
representations of every positive difference, simultaneously for every

  1 <= q <= N^k,  0 <= r <= N^k.

Public theorems:

* near_linear_normalized: the normalized quadratics;
* affineReps_bound: transfers capacity to actual affine squares;
* near_linear_affine: the actual maps n -> (q n+r)^2.

The affine transfer explicitly obtains D=qE with E>0 from any nonempty
positive-difference fiber. It does not assume arbitrary D is divisible by q.
An empty fiber is handled separately.

Exponent bookkeeping uses R=N^k(N^2+2N), R<=N^(k+3), and
|J|R<=N^(3k+4) for N>=2. The divisor estimate gives a uniform eventual
K=N^(epsilon/4). One can choose g>4(3k+4)/epsilon. With p=N^(-epsilon/2),
the deletion cost and the target both leave a fixed fraction of the mass.

This does NOT assert g=1 and does not improve the actual Sidon exponent.

## Verified obstruction to imposing capacity one at every shift

File: UniversalAffineSidonBound.lean

Public theorem universal_affine_bound:

If A subset [1,N] has Sidon affine-square images simultaneously for all

  1 <= q <= 4N,  0 <= r <= 2N^2,

then

  |A|^4 <= 48(N+1)^3.

First, all root-pair sums and square-pair sums must have compatible order.
If a+b<c+d but a^2+b^2>=c^2+d^2, put

  L=c+d-a-b, q=2L, r=a^2+b^2-c^2-d^2.

These coefficients are in the displayed ranges, and the two affine-square
pair sums are equal, contradicting the assumed Sidon property.

For each root-pair sum s, consider ordered pairs a<=b with a+b=s. Their
square sums have an integer interval hull. If there are k such pairs, the
spread of the first coordinates is at least k-1. The corresponding spread
of square sums is at least 2(k-1)^2. In particular k^2 is at most twice the
cardinality of this interval hull. Compatible ordering makes different
sum fibers' hulls disjoint, all inside [0,2N^2]. Cauchy-Schwarz over at most
2N+1 fibers, together with |A|^2 <= twice the ordered-pair count, gives the
stated bound. This argument is independently packaged as
monotone_pairs_bound.

Further public results:

* eventually_card_lt: the universal condition has cardinality < N^alpha
  eventually for every alpha>3/4;
* not_near_linear_universal_affine: negates the strengthened conjecture
  requiring ONE set to have Sidon images for all q,r<=N^3;
* single_shift_not_universal: the squares of {1,3,4,5} are Sidon, whereas
  the shift 2n+1 has 3^2+11^2=7^2+9^2. This uses trusted `decide +kernel`.

The strengthened negation is deliberately NOT called erdos_773.disproof.
It does not negate the original proposition. It rules out making the
simultaneous selection universally capacity one, not selecting a suitable
set for just one shift. There is no fixed-power upper bound here for the
actual unshifted Sidon maximum.

## Verification status

All eleven printed axiom audits in the three modules contain only
propext, Classical.choice, Quot.sound. No errors, admissions, or warnings
remain in these modules. The olean files have been built. Logs:

* /tmp/simultaneous-difference-final.log
* /tmp/simultaneous-affine-final.log
* /tmp/universal-affine-final.log

Spec.lean was checked separately; its old linter warnings and the original
admission warning remain. Its hash is unchanged:

917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

Main log: /tmp/spec-simultaneous-check.log.
