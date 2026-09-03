# Density-one parity self-count limits

## Original task status

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged
with its original sorry. No proof or disproof has been submitted.

## New verified files

* AbelSquarePrefixExplore.lean
* SquarePrefixDensityExplore.lean
* ParityDensityExplore.lean
* DensityDiagonalExplore.lean
* ParityDensityExceptionExplore.lean

All five compile with current oleans. ParityDensityAudit.log checks ten
principal declarations; only propext, Classical.choice, and Quot.sound occur.
No production file contains a sorry or added axiom. The three new *Checks.lean
files are scratch name searches with intentional failed checks, not dependencies.

## Abel-to-prefix transfer

For nonnegative f and a fixed natural k, assume the weighted series is
summable for 0<r<1 and

    [(1-r)/(-log(1-r))^2] sum_n f(n) r^(k(n+1)) -> 0.

Then

    sum_(n<N) f(n) / [N log^2 N] -> 0.

The radius is the previously checked r_N=1-1/N. Its normalization is exactly
1/(N log^2 N), and r_N^N -> exp(-1). Positivity gives the prefix lower bound
r_N^(kN) sum_(n<N) f(n) for the weighted series.

For a hypothetical witness A,c, with B={n:2n in A}, C={n:2n+1 in A}, let

    d(n)=r_B(n+1)-r_C(n).

The preceding twisted-energy result, with k=4, therefore yields

    sum_(n<N) d(n)^2 = o(N log^2 N).

Main declaration: Erdos66AbelSquarePrefix.witness_parity_prefix_zero.

## Fixed-tolerance exceptional counts

A general real sequence d with the preceding prefix estimate has, for each
epsilon>0,

    count({n: epsilon log(n+2)<=|d(n)|},N)/N -> 0.

An explicit checked bound, for K>0 and sufficiently large N, is

    count(bad,N)/N
      <= 1/K + (4/epsilon^2) sum_(n<N) d(n)^2/[N log^2 N].

Split the targets at N/K. At all later indices, once N>=K(K+1),
N<=(n+2)^2, hence log N<=2 log(n+2). Apply the squared-error bound to the
late targets, and charge the early ones by N/K. No rate of convergence or
power-saving exceptional bound is introduced.

## Separate parity ratios in density

The already checked pointwise combined self-count limit is

    [r_B(n+1)+r_C(n)]/log n -> c.

After replacing log n by log(n+2), combine it with the small contrast above.
If the sum ratio is within epsilon of c and the contrast is less than
epsilon log(n+2), both individual ratios are within epsilon of c/2.
Thus the UNION of their fixed-tolerance bad target sets has density zero.

Main declaration: Erdos66ParityDensity.witness_parity_self_counts_in_density.

## One common exceptional set

A general diagonal theorem is now checked for sequences in any pseudometric
space: statistical convergence implies convergence after replacing values
on one natural-density-zero exceptional set by the limit.

For tolerance 1/(j+1), choose a threshold L_j>=j+1 after which its bad-target
count ratio is bounded by 2^(-j). Let T_j be that truncated bad set. Each T_j
has density zero, and its count ratio has this bound at ALL cutoffs, since
cutoffs before L_j contribute zero. The union E of the T_j has density zero
by dominated convergence for the count ratios. Only j<N can contribute to
the cutoff at N, providing the finite union-cardinality comparison. Outside
E all sufficiently late points satisfy each fixed reciprocal tolerance.

Apply this theorem to the pair of parity ratios. The checked endpoint is:

    exists E, count(E,N)/N -> 0,
      (if n in E then c/2 else r_B(n+1)/log(n+2)) -> c/2,
      (if n in E then c/2 else r_C(n)/log(n+2)) -> c/2.

Main declaration:
Erdos66ParityDensityException.witness_parity_limits_off_density_zero.

The even index n+1 and the odd index n retain the exact odd/odd carry.

## Why this is not a solution

This establishes separate limits only OFF a density-zero set, not at every
sufficiently large target. The new diagonal theorem does not prove harmonic
summability of E, a power-saving bound, or the stronger deficit-weighted
summability required by the existing completion theorem.

Moreover the original all-target upper bound for the combined self-counts
does not imply an all-target upper coefficient c/2 for either component.
Thus both the sharp upper-control and weighted-deficit hypotheses needed
for the existing repair construction remain unavailable. No pointwise
coefficient-reduction operation, compatible infinite construction, or
universal contradiction has been obtained.
