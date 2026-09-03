# Least-prime-factor factorial congruence (verified, not a settlement)

`Submission/LambertMinFactorCongruence.lean` compiles, and its olean has been
built. It proves additional arithmetic properties of the original Lambert
coefficients A_m. It does not prove or disprove the conjecture.

## Uniform multinomial divisibility

For positive d and any k,

    k! * (d!)^k divides (d*k)!,
    k! divides (d*k)!/(d!)^k.

The first assertion is the integrality of the number of partitions into k
unordered blocks of size d. The Lean proof is arithmetic: induction on k uses

    choose(d*(k+1)-1,d-1)

to select the block containing a distinguished element. The binomial factorial
identity proves the induction step without introducing a quotient of a set.

The theorem names are `uniform_partition_denominator_dvd` (parameterized by
block size d+1) and `factorial_dvd_uniform_multinomial`.

## Application to Lambert coefficients

Let p=minFac(m), m>=2. In every proper-divisor contribution indexed by d>=2,
the quotient k=m/d is a divisor of m greater than one, so p<=k. Therefore

    p! divides k! divides m!/(d!)^(m/d).

The contribution d=m equals one. Summing the proper contributions gives

    A_m = 1 modulo (minFac(m))!.

This is `lambertCoeff_modEq_minFac_factorial`. Both printed axiom checks list
only propext, Classical.choice, and Quot.sound.

## Limitation

This congruence concerns the original coefficients A_m, whose scaled tails
are already verified to be too large for the existing small-tail descent
criterion. It has not been transferred to the rowwise coefficients c_m with
small tails. Indeed even the parity consequence fails for those coefficients:
`RowwiseFloors.lean` verifies c_6=2, while the new modulus at m=6 is 2!=2.

No new bound overcoming the original Lambert tails, and no infinite carry-
change result, has been proved. Submission/Spec.lean remains unchanged with
its original sorry. No proof or disproof has been submitted.

# Later limitation: simultaneous congruences admit a rational comparison

LambertCongruenceComparison.lean constructs different positive coefficients
c_n with rational total 1/6, prime values c_p=1, and a_n-1 | c_n-1 for every
n>=4, where a_n are the exact original Lambert coefficients. Thus every known
coefficient-to-one congruence is preserved simultaneously, including the
minFac factorial modulus. This does not preserve the original coefficients
or provide small polynomial tails, and is not a disproof of Erdős 68. See
LambertCongruenceComparisonNotes.md for the precise scope and verification.
