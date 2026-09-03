# Symmetry does not force modular pair matching

Erdős 773 remains UNSETTLED. Spec.lean was not changed. Its single sorry
remains for the unproved small-epsilon branch; the actual mathematical gap
is 0 < epsilon < 1/3. No proof submission was made in this continuation.

## New verified module

Submission/SymmetricResidueMatchingObstacle.lean imports only
FormalConjecturesUtil. It builds without warnings or admissions. All six
printed axiom audits use only propext, Classical.choice, and Quot.sound.
The corresponding .olean has been built.

Log: /tmp/symmetric-residue-matching-obstacle.log
Namespace: Erdos773.SymmetricResidueMatchingObstacle

## Finite example

The roots {1,2,3,10,11,12} are symmetric about 13/2, and their integer
squares are Sidon. Their square residues modulo 13 are {1,4,9}, which
are not Sidon because 1+4=9+9 in ZMod 13. Both assertions are kernel checked.

## Uniform affine family and unbounded prime centers

For every natural t, let

    p = 3t+302,
    A = {t+95,t+103,t+105,2t+197,2t+199,2t+207}.

The module proves all of the following, with no primality assumption:

* A has exactly six roots, all in [1,p-1];
* A is symmetric under a |-> p-a;
* the integer squares of A are Sidon;
* the square residues of A modulo p are NOT Sidon.

The Sidon proof is uniform in t, not a sample computation. For the six
linear root functions, record the three coefficients of every pair's
quadratic square-sum polynomial. A small finite certificate proves that
any two different unordered pairs have coefficientwise ordered polynomials,
with a strict constant-term inequality. Evaluation at any t>=0 preserves
that inequality.

The modular collision is the exact identity

    (t+95)^2+(t+103)^2+8p = 2(t+105)^2.

It is nontrivial modulo p: the further identity

    3(t+95)^2+20p = 3(t+105)^2+40

would force p to divide 40 if the first and third squared residues agreed.
This is impossible since p>=302. No field or prime cancellation is used.

Dirichlet's theorem supplies arbitrarily large primes p=2 mod 3; every such
p>=302 has p=3t+302 for a natural t. The theorem unbounded_prime_obstruction
therefore proves the failure at arbitrarily large PRIME reflection centers.
The prime bound and conversion to t are explicit Lean arguments.

## Scope

This disproves only the proposed implication from reflection symmetry and
integer square-Sidonness to modular square-Sidonness at the reflection
modulus. It supplies no upper bound for arbitrary large symmetric sets.
In particular its witnesses have constant cardinality six; it does not
exclude a stronger implication requiring near-linear cardinality.

The earlier symmetric extraction and fixed-power upper-bound transfer remain
conditional. No fixed-power upper bound for symmetric sets was obtained,
and no original Sidon lower exponent was improved.

Spec.lean still has SHA-256
f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0.
