# Prime-base carry investigation (not a solution)

The existing equivalence `irrational_iff_carry_changes` reduces the original
conjecture to infinitely many nonconstant factorial-grid steps. A stronger
possible statement would be that the step is nonconstant at every prime base.
That stronger statement is NOT proved.

In the indexing of Development.lean, constancy at base b means

    carry (b-2) = b-1,
    upperApprox (b-1) = upperApprox (b-2).

## Finite interval calculation

The script `/tmp/check_prime_carries.py 100000` uses exact integer intervals,
not floating-point estimates. It was extended from base 20,000 to base 100,000.
It found precisely these constant steps in its checked range 11 <= b <= 100000:

    52, 591, 1030, 1407, 1438, 2164, 4258, 10991, 21236.

All are composite. No cases were ambiguous in the interval calculation.
These finite checks have NOT been formalized in Lean and do not imply any
infinite assertion. In particular, the absence of a prime constant step in
this finite range does not establish the stronger statement above.

The computation encloses alpha using B=(100006)! and

    L = sum_(k=2)^100006 floor(B/(k!-1)),
    L/B < alpha < (L+100007)/B.

It compares factorial digits of that enclosure with exact rational bounds for
the scaled tail, allowing the carries of the finite rational sums to be read
off without constructing their very large common denominators. The log is
`/tmp/prime-carry-100000.log`.

## Verified arithmetic facts

PrimeSupport.lean now also proves, using Wilson's theorem,

    p | ((p-2)!-1),                       p prime, p >= 5,
    (exists n, p | ((n+2)!-1)) <-> p>=5,  p prime.

The first statement is `prime_dvd_denom_sub_four`, with the shifted `denom`
index p-4. The second is `prime_dvd_some_denom_iff`. Their printed axiom lists
contain only the permitted axioms.

For a prime p, the relevant scaled partial sum is

    X = (p-1)! * sum_(k=2)^(p-1) 1/(k!-1).

The next scaled sum is p*X+1+1/(p!-1). Constancy is a condition on the real
fractional part of X lying in a short interval. Wilson's congruence locates a
factor p in one of the rational denominators, but does not by itself control
this fractional part. No implication from the verified divisibility facts to
nonconstancy at primes has been obtained.

The original conjecture remains unproved; Submission/Spec.lean is unchanged.
