# Descending-factorial congruences for the exact Lambert coefficients

Verified auxiliary progress, NOT a proof or disproof of Erdős 68.
Spec.lean is unchanged and still contains its original sorry.

Two new files compile without warnings and have built oleans:

* Submission/LambertOffsetCongruence.lean
* Submission/LambertDescendingCongruence.lean

They contain no proof holes. The printed principal axiom audits list only
propext, Classical.choice, and Quot.sound.

## Uniform multinomial statements

Put U(d,k)=(d*k)!/(d!)^k, with d>0. The first file proves

    0<j<k and gcd(d*k,j)=1  ==>  d*k-j divides U(d,k).

The second file strengthens this to the full product:

    j<k and gcd(d*k,j!)=1
      ==> (d*k-1).descFactorial(j) divides U(d,k).

The product assertion is stronger than a list of separate divisibilities;
it does not presume that the consecutive offset factors are coprime.

## Proof mechanism

Let n=d*k and 0<j<k. Remove one element from each of j of the k equal-sized
blocks. The resulting multinomial V has j counts d-1 and k-j counts d,
and total n-j. A total divides each count times its multinomial. Hence
n-j divides both (d-1)*V and d*V, and therefore divides V.

The factorial identities give exactly

    U(d,k)*d^j = n.descFactorial(j)*V.

Consequently n.descFactorial(j+1) divides the left side. Coprimality of
n with j! implies that d is coprime to every n-i, 1<=i<=j. Thus d^j
can be canceled from the divisibility by (n-1).descFactorial(j).
All these arguments are checked in Lean; no p-adic estimate is required.

## Application to the original Lambert coefficients

Write

    a_n=sum_(d|n,d>=2) n!/(d!)^(n/d).

For n>=2 and 0<j<minFac(n), the first file proves

    a_n = 1 modulo n-j.

The second file proves, for every 0<=j<minFac(n),

    a_n = 1 modulo (n-1).descFactorial(j).

Every proper-divisor term has at least minFac(n) blocks. Also n is
coprime to j! in the stated range, so the uniform theorem applies to
each such term. The d=n term is exactly one.

In particular Lean verifies

    a_n = 1 modulo (n-1)*(n-2),  for every odd n>=3,

and the all-index modulus with j=minFac(n)-1.

Principal names:

* LambertOffsetCongruence.offset_dvd_uniform
* LambertOffsetCongruence.lambertCoeff_modEq_offset
* LambertDescendingCongruence.removed_blocks_identity
* LambertDescendingCongruence.descending_dvd_uniform
* LambertDescendingCongruence.lambertCoeff_modEq_descending
* LambertDescendingCongruence.lambertCoeff_modEq_minFac_descending
* LambertDescendingCongruence.lambertCoeff_modEq_odd_quadratic

## Scope and unresolved application

These are congruences for the exact original coefficients. They have NOT
been transferred to the rowwise-floor coefficients or to the positive
congruence-preserving small-tail carry. The original Lambert tails are
still too large for the available irrationality criteria.

The earlier rational comparison preserving every coefficient-to-one
congruence also warns against using these congruences without a new size
or inheritance argument. No small nonzero integer-form family or infinite
carry violation has been proved from the stronger modulus.

An external finite sanity check tested the uniform product statement for
d<30 and k<30 before formalization. It is not a premise: the Lean proof
is general and independent of that calculation. All computations and
compilations have completed. No complete informal solution is awaiting
formalization, and no original-conjecture submission has been made.
