# Checkpoint: sign-support route tested quantitatively

The original conjecture is STILL UNSOLVED. Spec.lean is unchanged and still
contains the original sorry. No irrational counterexample or sufficient
signed prime-pair/four-factor lower bound has been obtained. Do not submit
this auxiliary work as a settlement.

## Rough-support theorem audited

RemainderRoughSupport.lean, namespace Erdos972RemainderRoughSupport, was
already compiled at the previous checkpoint. AuditRoughSupport.lean now
separately checks its principal declarations.

For n>0, U>0, U,V <= D, and gcd(n,D!)=1:

    A_UV(n) = log n,
    R_UV(n) = Lambda(n) - log n <= 0.

Thus positive R_UV(n) requires a prime factor <= max(U,V). Products of two
remainders are nonnegative on jointly rough inputs. The remaining nonrough
sum was retained without a mass bound; centering remains an additional
correction.

## New exact positive family

RemainderPositiveMass.lean, namespace Erdos972RemainderPositiveMass:

    typeIIPart_three_primes

For distinct primes r,s <= W with rs>W, and prime q>W:

    R_WW(rsq) = log q > 0.

Proof: the only surviving large Mangoldt divisor in the final convolution
is q. The other coefficient at rs is 1, since mu(rs)=1 and the only smaller
divisors 1,r,s lie below the cutoff. This is the actual Vaughan remainder,
not an unrelated arbitrary-coefficient model.

## Reciprocal-prime bands

PrimeReciprocalBands.lean, namespace Erdos972PrimeReciprocalBands:

    reciprocalPrimeMass a b = sum_{a<p<=b, p prime} 1/p.

The dyadic count bound gives mass >= 1/(4 log(2x)) on (x,2x]. Summing dyadic
bands proves a finite power-band lower bound. Consequently, eventually in k:

    reciprocalPrimeMass (2^(5k)) (2^(6k)) >= 1/24,
    reciprocalPrimeMass (2^(6k)) (2^(7k)) >= 1/28.

Only previously verified qualitative PNT is used; no prime-pair estimates.

## Finite positive-mass lower bound

RemainderPositiveBudget.lean, namespace Erdos972RemainderPositiveBudget:

    positiveMass W N = sum_{0<n<=N} max(R_WW(n),0).

Theorem positiveMass_lower: let A,C be finite prime sets below W, with
r<s and rs>W for every r in A,s in C. Suppose the dyadic theta lower bound
holds above B and 4 W^2 max(W,B) <= N. Then:

    positiveMass W N >= (N/8)*(sum_{r in A}1/r)*(sum_{s in C}1/s).

For each (r,s), take q prime in (Q,2Q], Q=floor(N/(2rs)). The numeric
hypothesis ensures Q>=max(W,B), and N<=4rsQ. The theta lower bound gives
sum log q >= Q/2 >= N/(8rs). Unique prime factorization, the ordering r<s,
and q>W prove that all triples map injectively into n<=N. Thus no terms
are double-counted.

## Actual growing scales: positive mass is NOT o(N)

RemainderPositiveScales.lean, namespace Erdos972RemainderPositiveScales:

Use k=floor(log_2 W / 8). Then 2^(8k)<=W<2^(8(k+1)). For k>=3, the two
prime bands above are below W, separated, and every cross-product rs is >W.
Their reciprocal masses yield:

    positiveMass W N >= N/5376.

The theorem eventually_positiveMass_lower applies this at precisely

    N = Erdos972CenteredRowScales.scaleCutoff alpha u,
    W = Erdos972GrowingTypeIIReduction.growingCutoff u.

For every fixed alpha>=1, eventually in u:

    (N : R)/5376 <= positiveMass W N.

This uses the earlier W^640<=N bound, which easily supplies the numeric
hypothesis for sufficiently large W. No irrationality is needed, so the
bound also holds at the irrational good scales.

Theorem not_tendsto_positiveMass_zero formally proves that

    positiveMass W N / N

does NOT tend to zero.

## Exact interpretation and remaining gap

This rules out discarding all positive remainder values as an o(N) mass
error merely because they have small prime factors. It is stronger than
one numerical positive example, and it concerns the actual growing cutoffs.

It does NOT rule out all sign-specific covariance estimates. In particular:
- It is a ONE-COORDINATE L1 lower bound, not a signed two-coordinate estimate.
- It supplies neither an upper bound for the negative product contribution
  nor control of the centering correction.
- It does not show that the sign-support raw lower bound is sufficient.
- The strict centered four-factor gap in ProgressFourFactor.md remains an
  unproved hypothesis.

All principal new declarations compile and audit with only propext,
Classical.choice, Quot.sound. Audit file: AuditPositiveMass.lean.
