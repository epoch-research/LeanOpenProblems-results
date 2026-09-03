# Original twice-prime congruence modulo the prime square

Verified auxiliary arithmetic, NOT a proof or disproof of Erdős 68.
Submission/Spec.lean is unchanged and still contains the original sorry.

## Original coefficient identity

For an odd prime p, the divisors of 2p give the exact formula

    a_(2p) = (2p)!/2^p + choose(2p,p) + 1.

The new file `LambertTwicePrimeSquare.lean` proves this as
`twice_prime_formula`. It then proves

    a_(2p) = 3 (mod p^2).

The first summand vanishes modulo p^2: p^2 divides (2p)!, while p is
coprime to 2. For the middle summand, Vandermonde gives

    choose(2p,p) = 2 + sum_(k=1)^(p-1) choose(p,k)*choose(p,p-k).

Both binomial factors in every interior summand are divisible by p.
Thus `central_choose_mod_square` gives the middle congruence modulo p^2.
No unproved strengthening of Lucas or Wilson's theorem is used.

Main declaration:

    lambertCoeff_twice_prime_square

## Verified failure of square-congruence inheritance

Combining the original congruence with the existing unconditional result
`CarriedSquareCongruenceBarrier.twice_square_not_congruent` proves
`carried_twice_prime_square_defect`:

For p prime, p>=7, and 2p-1 nonprime,

    p^2 does NOT divide
      CongruencePreservingCarry.coeff(2p) - a_(2p).

This is unconditional: it does not assume that the target sum is rational.
It explains why the original square congruence cannot be added to the
already constructed small-tail representation. It is NOT a proof of
infinitely many original factorial-grid carry changes. The carries and
coefficients in those two criteria are different objects.

The new file compiles, has a built olean, and its two principal axiom audits
contain only propext, Classical.choice, and Quot.sound. No new axiom or proof
hole was introduced. No complete proof or disproof of Spec.lean has been
obtained or submitted.
