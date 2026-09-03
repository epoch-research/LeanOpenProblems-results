# Exact-bracket rank-assigned one-target repair

## Main task status

The existential conjecture in Submission/Spec.lean is neither proved nor
disproved. Its original import, statement, and sorry are unchanged. No valid
proof submission is available. The results below are conditional one-target
repairs, not simultaneous repairs of an arbitrary exceptional set.

## Production files

* AssignedPacketRepairExplore.lean
* AssignedPacketDegreeExplore.lean
* AssignedIntervalRepairExplore.lean
* RankProfileGapExplore.lean
* GlobalRankPacketRepairExplore.lean

All five compile and have current oleans. RankPacketRepairAudit.lean checks
all twelve lemma/theorem declarations; its saved log contains only propext,
Classical.choice, and Quot.sound. Some harmless linter warnings remain in
the two earlier assigned-degree/interval files. No production placeholders
or new axioms were introduced.

These results use the already compiled exact rank-cell exchange lemmas in
RankCellExchangeExplore.lean and its dependencies. RankExchangeAudit.lean
separately checks those earlier exchange results.

## Arbitrary assignments and finite packets

The finite symmetric-packet selector now accepts any assignment from
candidate endpoints to deleted old points, not just predecessors. The
assignment must map into the old set, have bounded fibers, and assign the
two endpoints of each packet to distinct old points. It retains the full
signed collateral estimate, including both deleted/old and inserted/old
contributions.

The output has D=assign(F), assignment injective on F, and

    |D|=|F|=2m,
    r_new(n)=r_old(n)+2m,
    r_F(z)<=6 for z!=n.

The degree of either forbidden or tested candidates is at most

    2V+2H r_old(z),

when each endpoint map is injective in a width-W interval with old occupancy
at most V and assignment fibers at most H. No unproved difference-correlation
bound has been assumed.

If both assignment distances are less than H, the fiber bound is 2H.
The interval selector uses the explicit budget

    [m^4+8m^2 H+m(2 sqrt(2WV)+4HV)]/W
      + |T| exp(m exp(t)(2 sqrt(2WV)+4HV)/W-tR) < 1.

All tested signed errors are then less than 4R+6.

## Nearby rank assignment

Write P(u)=sum_(i<u) p(i), and assign an omitted u to the old point of
zero-based rank floor(P(u)). Exact brackets imply that every natural rank
exists for the harmonic profile. For antitone nonnegative p, a unit-mass
condition

    1 < H p(u+H)

bounds both assignment distances by 2H. The harmonic specialization applies
uniformly to u<=12N if H<=N and 2 sqrt(16N+1)<H.

Distinct assigned old points give distinct cumulative-rank cells. The
previous rank_family_brackets theorem therefore preserves ALL original
floor/ceiling brackets for the simultaneous finite packet. There is no
additional discrepancy unit.

## Global one-target theorem

Erdos66GlobalRankPacketRepair.eventually_global_rank_packet_repair assumes

    floor(P(X)) <= count(A,X) <= ceil(P(X)) for every X,
    r_A(z) <= K+C log(z+2), K,C>=0.

For every M>=0 and epsilon>0, eventually in N, every natural m<=M log N
admits finite E,F such that

* E is a subset of A and F is disjoint from A;
* |E|=|F|=2m;
* every modified point lies in [2N,14N];
* the new set satisfies the SAME original brackets at every cutoff;
* r_new(16N)=r_A(16N)+2m;
* for EVERY z!=16N,

      |r_new(z)-r_A(z)| <= epsilon log(z+2).

The proof takes H=gapSize(1,N), absolute assignment gap 2H, and fiber
bound 4H. Eventually H<=N and 4H<=100 sqrt(N). Thus the old analytic
selection budget applies with that larger constant. The old set is truncated
at X=N^h+1 with h>=2 and epsilon*h>=4M. Assignment membership in the cutoff
is proved from the rank gap and the support bound.

Below 2N there is no change. Targets below X are included in the finite
sampling test set. At all remaining targets, the generic finite-edit bound
4m is at most epsilon log(z+2). The theorem does not silently extrapolate
a finite test set to an unchecked infinite tail.

## Remaining obstruction

This removes the exact-bracket defect of the preceding one-target
predecessor repair. It does not settle Erdős 66:

* the target centers are 16N, individually chosen above eventual bounds;
* the operation increases the central count, not a general signed tuning;
* it gives no dense simultaneous repair or cumulative-collateral theorem;
* the existing power-saving exceptional-set bounds do not supply the
  sparse repair schedule required by the earlier separated iteration;
* no sharp all-target upper coefficient or uniformly sublogarithmic
  quadratic Boolean-rounding error has been obtained.

Choosing successive tolerances before sufficiently large adaptive centers
would only give a sparse construction. It cannot be substituted for
repairing every actual exceptional target. None of the auxiliary
counterexamples in this project negates the original existential statement.

## Subsequent coordinated extension

AdaptiveRankRepairProgress.md records a completed extension to arbitrary lists
of comparable centers with total demand S(N) satisfying S(N) log N/sqrt N->0.
It uses sequential cell exclusion and a common collateral potential. Exact
brackets and every-natural-target bounds are retained, uniformly in the host.
Thus coordinated sub-square-root batches are now available; dense arbitrary
exceptions and the original conjecture remain unresolved.
