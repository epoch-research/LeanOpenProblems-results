# Simultaneous logarithmic-size exact-bracket downward batches

## Original task status

Erdős 66 is still neither proved nor disproved. `Submission/Spec.lean` is
unchanged and contains its original `sorry`. No valid submission is ready.

## Verification

Seven new production files compile without warnings and have current oleans:

1. QuadraticLogWindowBudgetExplore.lean
2. RankRestorationSelectionExplore.lean
3. RankRestorationAlgebraExplore.lean
4. GlobalRankRestorationExplore.lean
5. BatchCentralDeletionExplore.lean
6. BatchRankDownwardClippingExplore.lean
7. BatchRankHostClippingExplore.lean

`BatchRankDownwardAudit.lean` checks all 11 theorem/lemma declarations. Its
saved log lists only propext, Classical.choice, and Quot.sound.

## Common-potential restoration of an arbitrary prescribed deletion set

The new finite rank-restoration selector does NOT require all deleted points
to be partners at one central target. Every selected candidate row still
corresponds to one prescribed old rank, and all rows are distinct. One common
potential controls the insertion load

    2*pairs(F,A,z) + r_F(z).

The budget has been strengthened from O(log N) to O(log(N)^2) total
replacements, while retaining candidate windows of width ceil(log(N)^8).
The numerator of the mean cost has order log(N)^7, whereas the denominator
has order log(N)^8. This is proved by the explicit finite budget inequality.

`Erdos66GlobalRankRestoration.uniformly_eventually_rank_restoration` is uniform
over hosts satisfying all exact harmonic brackets and a fixed logarithmic
representation envelope. Any prescribed old deletion set D in [2N,5N] with
|D|<=M log(N)^2 can be reinserted as F, where:

* |D|=|F|, F is disjoint from A;
* all modifications lie in [N,6N];
* every original exact prefix bracket holds for (A\D) union F;
* at EVERY natural target z,

      0 <= r_((A\D) union F)(z)-r_(A\D)(z) <= epsilon log(z+2).

The comparison is against the DELETED CORE, not against A. Thus the theorem
does not claim deletion losses are small. The far-target insertion estimate
compares inserting F into A\D with inserting F into A, then applies the
previous short-support tail theorem to the latter. It does not apply an
exact-bracket hypothesis to the non-bracketed deleted core.

## Batch deletion algebra

For a finite center set T and chosen upper-endpoint deletions D_n, let
D be their union. Overlaps are allowed. The exact own-center decrement is
separated from other centers:

    r_(A\D)(n) <= r_A(n)-2|D_n|,

    r_A(n)-2|D_n| <= r_(A\D)(n)
        + 2 sum_(m in T\{n}) fiber(A,cutoff(m),m,n).

At any target z, the total deletion loss is at most twice the sum of the
corresponding host triple fibers. No disjointness of the D_n or independent
selection of their points is assumed.

## Uniform simultaneous clipping theorem

`Erdos66BatchRankDownwardClipping.uniformly_eventually_batch_downward_clipping`
chooses its large-N threshold BEFORE the host and the batch. Assume:

* every n in T lies in [4N,5N];
* |T| <= log N;
* 2 R |T| <= (epsilon/2) log N;
* for every n in T, all its distinct-target triple fibers through N^33
  have cardinality at most R;
* each integer cap q(n) is at least 2 boundary(A,d(n),n)+6.

Then ONE pair D,F preserves all exact brackets and satisfies, at all n in T,

    min(r_A(n),q(n)-1) <= r_new(n) + epsilon log(n+2),
    r_new(n) <= q(n) + epsilon log(n+2).

At EVERY z outside T,

    |r_new(z)-r_A(z)| <= epsilon log(z+2).

Every center's deletion set is chosen against the original host. All of them
are unioned before the rank restoration. Insertion errors are controlled by
one potential for the entire union, not by adding per-center repair errors.
All modifications lie in [N,6N], and the tail beyond N^33 is checked.

## One-host consequence

`Erdos66BatchRankHostClipping.exists_host_with_logarithmic_batches` produces
ONE A with exact harmonic brackets and all reciprocal-integer power-cost
rows. For every c>0 and epsilon>0 there is rho>0 such that, eventually in N,
EVERY T subset [4N,5N] with |T|<=rho log N admits the above simultaneous
clipping with q(n)=floor(c log n).

One explicit choice is

    rho = min(1, epsilon/[4(tripleCap(34)+1)]).

The boundary cutoff and large-N threshold depend on c and epsilon; A does
not. The finite modifications can depend on the whole requested batch T.

## Remaining gap

This is a simultaneous theorem, but only for logarithmic-size batches.
Available power-saving estimates on shrinking-tolerance exceptional sets do
not establish this size bound. Their weakness is not a lower bound on the
number of exceptions for every possible host.

The new theorem does not justify an arbitrary sequence of batches: triple
sparsity must be checked for the actual current host. Nor does clipping fill
an already deficient target. The earlier positive batch theorem has a much
larger sub-square-root packet range, but still does not cover the known
exception estimates at every tolerance.

No all-target finite-prefix feasibility with fixed thresholds, infinite
dense repair schedule, or contradiction to a hypothetical witness has been
proved. These results must not be submitted as a resolution of Spec.lean.
