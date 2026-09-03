# Rough pairwise norms: verified extraction and limitations

The original Erdos 773 conjecture is NOT settled. The new work does not
improve the actual Sidon exponent and does not disprove the conjecture.
`Spec.lean` has not been changed. Its completed unconditional result is
still eventual M(N) >= N^(2/3), and its sole admission remains the range
0 < epsilon < 1/3.

## New clean modules

- `RoughPairNorms.lean`
- `LogRoughPrimeCarrier.lean`
- `RoughPrimeCollisions.lean`
- `LogRoughPrimeCollisions.lean`

All four compile without warnings or admissions and have built oleans.
The eleven printed public-result audits use only `propext`,
`Classical.choice`, and `Quot.sound`. None imports the admitted Spec theorem.

## Finite coloring

For an odd prime p and a root n which is nonzero modulo p, orient the two
residues n^2 and -n^2 by their canonical natural representatives. This gives
a Boolean color. If a^2+b^2 is zero modulo p, the two colors differ.

For a finite collection P of odd primes and a finite root set A consisting
of units at every p in P, pigeonholing the vector of these colors gives
B subset A such that

    |A| <= 2^|P| |B|,

and no a^2+b^2, for a,b in B, is divisible by any p in P. Repeated pairs
are included.

For prime roots, deleting just P itself supplies all unit hypotheses.
`prime_extraction` combines this with the existing elementary prime-count
lower bound. `eventually_prime_carrier` proves a uniform consequence: for
0 < delta <= 1, eventually for every P with

    |P| <= (delta/4) log n,

there is B subset sievePrimes(n) with |B| >= n^(1-delta) and the above
pair-norm roughness. Here sievePrimes(n) consists of primes between 5 and
2n, inclusive.

Using Mathlib's Chebyshev upper bound, `LogRoughPrimeCarrier.eventual_carrier`
proves: for every fixed K>0 and 0<delta<=1, eventually there is a prime-root
set B subset [1,2n], |B| >= n^(1-delta), such that every a^2+b^2 with a,b in B
has no odd prime factor p <= K log n.

These are near-linear CARRIERS, not Sidon sets.

## Explicit nonprime-root limitation

The existing quadratic-height common-residue collision, with modulus
Q=product(P), supplies four different positive roots whose pairwise norms
are all 2 modulo every p in P. Its height is at most 10Q^2+7Q+1.

The new `logarithmic_rough_collision` specializes this and uses
primorial(k) <= 4^k. For every k there are

    0 < a < d < c < b <= 18*16^k,
    a^2+b^2 = c^2+d^2,

while every pairwise norm from these four roots has no odd prime divisor
at most k. This is an explicit logarithmic-cutoff obstruction; the roots
are not asserted prime.

## Prime-root limitations, including a growing cutoff

A tag in Option(P) separates the excluded prime roots themselves. In a
four-distinct monochromatic collision, this tag must be `none`, so all
four prime roots are units at all excluded primes. The vector color then
makes all pairwise norms rough.

`RoughPrimeCollisions.eventually_prime_rough_collision` verifies such a
four-distinct prime collision for every fixed P, at every sufficiently
large bit length, by applying the previously proved prime-color collision
theorem. Its type explicitly includes FourCollision, not just failure of
Sidonness on a four-element set.

The stronger new theorem

    LogRoughPrimeCollisions.eventually_logarithmic_prime_collision

proves, eventually for every k, a four-element prime-root set contained in
sievePrimes(2^(65536*k)), with an explicit FourCollision property and all
pairwise norms free of odd prime factors at most k. Thus all roots are at
most 2^(65536*k+1), and the cutoff is a fixed positive multiple of the
logarithm of this height bound.

For this last proof, Chebyshev gives |P| <= 4k/log k. The tagged color count
is 2^|P| (|P|+1). At bit length 65536*k, the existing primorial Sidon upper
bound supplies exponential loss at least 32k/log k. This beats the color
cost exp(4k/log k) and the polynomial factors; the remaining entropy cost
is bounded by

    (128*3*65537) k^2 exp(-sqrt(k)),

which tends to zero. Every estimate is checked in Lean.

## What this does not establish

The prime-root counterexamples disprove only the blanket assertion that
logarithmic pair-norm roughness suffices for Sidonness. They do not imply
that every rough carrier, or every large subset of one, has a collision.
The small constant in the growing-cutoff counterexample is explicit; no
counterexample for every arbitrarily large fixed logarithmic coefficient
is claimed here.

No bound reducing the surviving four-support count to N^(1+o(1)) was
obtained. Excluding primes up to a logarithmic cutoff has not supplied a
fixed-power saving in the collision count. No unrestricted fixed-power
upper bound on M(N) has been obtained either.

## Logs and original-file state

- /tmp/rough-pair-norms.log
- /tmp/log-rough-prime-carrier.log
- /tmp/rough-prime-collisions.log
- /tmp/log-rough-prime-collisions.log
- /tmp/spec-rough-norm-review.log

The main file still has its sole `import FormalConjecturesUtil`, theorem
at line 17276, and sole admission at line 17287. Its SHA-256 remains:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940

No incomplete main proof has been submitted as a settlement.
