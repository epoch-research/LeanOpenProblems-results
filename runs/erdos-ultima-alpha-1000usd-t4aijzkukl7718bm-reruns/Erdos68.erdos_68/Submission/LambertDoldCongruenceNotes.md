# Prime-power Dold congruences (verified auxiliary result)

This is NOT a settlement of Erdős 68. Spec.lean is unchanged. No proof or
disproof of its conjecture has been obtained or submitted.

LambertDoldCongruence.lean compiles without warnings. Its four principal
printed axiom audits use only propext, Classical.choice, and Quot.sound.
The full current source has a rebuilt olean.

For a_n = sum_{d|n,d>=2} n!/(d!)^(n/d), put F_n=a_n+n! for n>0.
For every prime p, r>=0, and m>0, the file proves

    F_(p^(r+1)*m) == F_(p^r*m) (mod p^(r+1)),
    a_(p^(r+1)*m) == a_(p^r*m)+(p^r*m)! (mod p^(r+1)).

The singleton correction on the second right-hand side must not be dropped.
These strengthen LambertPrimePowerScaling's congruences modulo p.

## Proof

Write U(d,k)=(d*k)!/(d!)^k as the coefficient of X_1^d...X_k^d
in (X_1+...+X_k)^(d*k). Frobenius modulo p, followed by the general
power-lifting divisibility lemma, gives for integer multivariate polynomials

    p^(r+1) divides f^(p^(r+1)*m)-expand_p(f^(p^r*m)).

Extracting balanced coefficients gives

    U(p*d,k) == U(d,k) (mod p^(r+1))

when p^(r+1) divides p*d*k. If p does not divide d and p^(r+1)
divides d*k, then p^(r+1) divides k, hence k!, hence U(d,k).
Split the divisor sum for F into p-divisible and p-coprime block sizes;
reindex the former by d -> p*d. This proves the first congruence.
The larger index's singleton factorial is divisible by the modulus,
which yields the second congruence.

Principal declarations:
* coefficient_sum_X_pow
* uniform_prime_power_lift
* fullCoeff_dold
* lambertCoeff_dold

## Missing bridge

These are congruences of the original coefficients. They have NOT been
transferred to the congruence-preserving small-tail carry, and no sufficiently
small-tail carry preserving all these congruences has been constructed.
The result alone does not imply irrationality.
