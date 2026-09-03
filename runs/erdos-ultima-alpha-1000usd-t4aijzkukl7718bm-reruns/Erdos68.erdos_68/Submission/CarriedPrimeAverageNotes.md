# Averaged necessary behavior of the actual carried prime tails

Verified auxiliary work, NOT a proof or disproof of Erdős 68.
Spec.lean remains unchanged with its original sorry. Nothing has been submitted.

CarriedPrimeAverage.lean compiles without warnings, has a built olean, and
contains no proof holes. The printed principal axiom audits use only
propext, Classical.choice, and Quot.sound.

## Definitions and verified estimate

Let p_i be the primes starting at five, and T_n the actual factorial-scaled
tails of CongruencePreservingCarry.coeff. Put

    D_i = (p_i^2-T_(p_i))/p_i^3.

The known strict quadratic bound gives D_i>0, without any rationality
hypothesis.

If the original sum equals a rational q and q.den<=p_i-1, the exact
prime-gap pattern gives, with p=p_i and s=p_(i+1),

    T_s = s(2p-s)-1,
    D_(i+1) = 2(s-p)/s^2 + 1/s^3
              <= 3(1/p-1/s).

The file verifies that the enumerated primes are consecutive and that
s<2p, using Bertrand's theorem. The displayed analytic inequality itself
needs only p>=1 and s>=p+1. Summing the reciprocal differences telescopes.

Consequently, under the same denominator condition at p_N,

    sum_(i=0)^(k-1) D_(N+1+i)
        <= 3(1/p_N-1/p_(N+k)) <= 3/p_N,

and

    sum_(i>=0) D_(N+1+i) <= 3/p_N.

In particular, rationality forces Summable deficit.

## Main declarations

* rational_prime_tail
* rational_deficit_succ_bound
* rational_block_bound
* rational_summable_deficit
* rational_tsum_bound
* irrational_of_not_summable_deficit
* irrational_of_frequent_block_violations

The last criterion only requires arbitrarily late finite blocks whose
weighted deficit exceeds 3/p_N. It does not require a uniform pointwise
bound at all primes.

## Missing application

Neither non-summability of the actual deficits nor arbitrarily late block
violations has been proved. Positivity of each deficit does not imply
non-summability. This result is an averaged consequence of the existing
conditional prime-gap pattern, not an independent contradiction to that
pattern or a settlement of the original conjecture.
