# Large-divisor block moments — genuine estimates, not a settlement

Spec.lean is unchanged with the original sorry. No proof of the conjecture
or irrational counterexample has been found. No incomplete proof was
submitted.

New file: LargeDivisorBlockMoment.lean.
Namespace: Erdos972LargeDivisorBlockMoment.
All principal declarations compile and audit with only propext,
Classical.choice, and Quot.sound.

Write R_d = sum_{0<p<=N, d|floor(alpha*p)} primeWeight(p), and let
D<d<=2D be a divisor block. All weights are the actual prime weights.

## Complementary-divisor switching

`block_divisor_card_le_cofactor_card` and `block_firstMoment_switch` prove,
for alpha>=1, D>0 and floor(alpha*N)<=D*K,

    sum_{D<d<=2D} R_d
      <= sum_{0<k<=K} row(k, min(N,2*D*k)).

The map d -> floor(alpha*p)/d is injective for each positive input.
The SHORTENED prefix min(N,2*D*k) is important: replacing every prefix by N
would introduce an unnecessary harmonic logarithm.

`block_firstMoment_upper` shows that actual small-row upper bounds

    row(k,X) <= 7X/k + E  (0<k<=K, X<=N)

give the log-free first moment

    sum_{D<d<=2D} R_d <= K*(14D+E).

## Row multiplicity and second moments

`prime_row_upper_of_large_divisor` proves

    R_d <= M*log N

provided M>0, N<=d*M, and alpha*M<d. The last condition ensures that every
input contributing to the row exceeds M, so the modular injection applies
to the FULL row, not just its truncated part.

`block_secondMoment_upper` combines the bounds. If additionally
alpha*M<D and N<=D*M, then

    sum_{D<d<=2D} R_d^2 <= M*log N * K*(14D+E).

## Actual irrational good scales

`exists_large_block_moment_scale` has NO unproved row estimate as a
hypothesis. For every alpha>1 irrational and B, it finds u>B, u>0, with
N=u^6 such that, SIMULTANEOUSLY for every D,K,M satisfying

    D>0, M>0, K<=root64(u), floor(alpha*N)<=D*K,
    alpha*M<D, N<=D*M,

one has

    sum_{D<d<=2D} R_d <= 14D*K+N,
    sum_{D<d<=2D} R_d^2 <= M*log N * (14D*K+N).

Proof selects an actual rational approximant to alpha, reuses the existing
uniform-prefix Mangoldt rows, and bounds primeWeight by Mangoldt. Thus the
one-sided upper estimate does not need a proper-prime-power subtraction.
The existing scale budget gives E*root64(u)<=N.

For choices K of size alpha*N/D and M of size N/D, these are upper bounds
of size O_alpha(N) and O_alpha(N^2/D*log N). The stated modulus range
restricts the usable blocks; it must not be extended to all D.

## Centered square errors

`block_centeredEnergy_le_secondMoment` proves the valid upper bound

    sum_{D<d<=2D} (R_d-psi(N)/d)^2
      <= sum_{D<d<=2D} R_d^2 + 49N^2/D.

Here the negative cross term is bounded above by zero using positivity;
no cancellation of that term is asserted. The mean-square cost is explicit.

`exists_large_block_dispersion_scale` gives, on arbitrarily large actual
good scales and under the SAME block-size conditions,

    sum_{D<d<=2D} (R_d-psi(N)/d)^2
      <= M*log N*(14D*K+N) + 49N^2/D.

## Unresolved step

These are upper moments in a large-divisor range below N. They do not yet
provide a sufficiently small signed coefficient error, the centered
four-factor lower gap, or any prime-pair lower bound. The original universal
conjecture remains unresolved.
