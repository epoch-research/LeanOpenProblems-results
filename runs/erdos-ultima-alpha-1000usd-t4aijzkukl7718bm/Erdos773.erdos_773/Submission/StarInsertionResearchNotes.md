# Polynomial-height obstruction to uniformly cheap insertion

This does NOT settle Erdos 773. Spec.lean is unchanged, with its original
statement and sole admission. No incomplete proof has been submitted.

## New verified modules

- QuantitativeRotationSpecialization.lean
- StarInsertionObstruction.lean

Both compile without warnings or admissions and have built oleans. The
printed audits use only propext, Classical.choice, and Quot.sound.
Logs: /tmp/quantitative-rotation-final.log and /tmp/star-insertion-final.log.

## Quantitative specialization

For a finite family of m multivariate rational polynomials, each of total
degree at most D, bounded_pair_specialization supplies natural coordinates
in (3Q,4Q], Q=D*m^4+1, preserving every equality between two pair sums in
both directions. Multiply all nonzero pair-sum differences (replace the
zero differences by 1). The product is nonzero and has total degree at
most D*m^4. The combinatorial Nullstellensatz guarantees a nonzero value
on the Q-point integer grid in every coordinate. No random computation or
unproved generic specialization is used.

Apply this to any injective finite restriction of the previously classified
3-4-5 rotation model. Every squared form has degree at most 2. The theorem
bounded_model gives positive, injective integer roots of height at most
28*(2*m^4+1), with all square-pair relations preserved. The natural subtraction
in 4*x_i-3*x_j is justified by the coordinate bounds.

## Star obstruction

For each natural k, insertion_cost constructs an actual positive natural
root x and a root set S such that:

- |S|=3*k and x is not in S;
- all roots in S union {x} are at most H=28*(2*(3*k+1)^4+1);
- the square values of S are Sidon;
- if T is a subset of S and the square values of T union {x} are Sidon,
  then |T|<=2*k.

The formal center is 5*X_0. Each leaf i contributes the three forms

    5*X_i, 3*X_0+4*X_i, 4*X_0-3*X_i.

Their squares make one trade with the center. The established formal
classification shows that omitting the center leaves a Sidon set: every
nontrivial relation would be a star trade and would need the missing center.
The bounded specialization retains that exact property. Inserting the
center forces omission of at least one of each of the k disjoint triples.

For k>=1, height_bound proves H<=15000*k^4. The public theorem
 deletion_power_obstruction additionally proves that any R subset S whose
deletion permits inserting x satisfies

    k <= |R|,    H <= 15000*|R|^4.

Thus the obstruction has polynomial height; it does not rely on unspecified
large denominators. In particular, it excludes a uniform subpower-in-height
bound for the cost of inserting every outside root into every Sidon square
carrier.

## Scope

The construction does NOT show that every outside root is expensive, that
a particular optimization algorithm must choose x, or that a maximum Sidon
set has this configuration. It does not bound the unrestricted maximum
among all squares up to H^2. Its carrier has size on the order of H^(1/4),
not near-linear size. Neither the original lower exponent nor an unrestricted
upper exponent has improved. This is not the required negation of Erdos 773.

Spec.lean SHA-256 remains:
f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0
