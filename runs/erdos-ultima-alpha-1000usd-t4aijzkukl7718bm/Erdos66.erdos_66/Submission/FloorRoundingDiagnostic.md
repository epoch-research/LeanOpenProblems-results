# Targeted diagnostic of the floor-rounded harmonic profile

## Status and scope

The conjecture is still **not proved or disproved**. `Spec.lean` is unchanged
and contains its original `sorry`. This note records a numerical diagnostic,
not a theorem or a certified counterexample.

The exact Lean results in `FractionalProfileExplore.lean` and
`RoundingExplore.lean` remain valid. In particular the sufficient quadratic-error
hypothesis is still **unproved**.

## Candidate examined

The specific set is obtained by flooring cumulative sums of the fractional
profile with P(z)^2 = -log(1-z)/(z(1-z)). The script
`Submission/profile_diagnostic.py` approximates the coefficients by a Cauchy/FFT
calculation and then computes the finite indicator convolution by FFT.

Internal checks in one run:

- First 80 coefficients compared with exact rational square-root recurrence:
  maximum numerical difference approximately 4.1e-14.
- Fractional convolution compared with H_{n+1} through 2^20 terms:
  maximum residual approximately 1.7e-8.
- Computed floor increments were all 0 or 1.

These checks do NOT constitute a rigorous interval-arithmetic or Lean
certification of every floor decision in the full calculation.

The diagnostic reported unrepresented targets in each tested dyadic block. In
the block [2^19,2^20), it reported 402 such targets and representation counts
ranging from 0 to 46. The mean of r(n)/log n was close to 1, while the maximum
was about 3.42. Smaller tested blocks showed similar qualitative behavior.

## What may and may not be concluded

This motivates caution about trying to prove the missing uniform estimate for
the unmodified floor rounding. It does NOT prove infinitely many holes, failure
of its asymptotic limit, or failure of any other rounding. In particular it is
not a disproof of Erdős 66.

No rigorous persistence theorem for the observed deviations and no uniformly
controlled repair construction has been obtained.
