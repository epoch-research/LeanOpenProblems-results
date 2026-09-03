# Sublogarithmic clipping and uniform thresholds over a sparse menu

## Original task status

The existential conjecture in `Submission/Spec.lean` remains unresolved.
Its import, statement, and original `sorry` are unchanged. These auxiliary
results are not a proof or a disproof of that conjecture.

## Verified production files

* SublogRankDownwardRepairExplore.lean
* SublogDownwardClippingExplore.lean
* SublogHostClippingExplore.lean
* ClippableSparseRestorationMenuExplore.lean

All four compile with current oleans and no warnings. Their seven lemma/theorem
declarations are audited in SublogClippingAudit.lean and its saved log, using
only propext, Classical.choice, and Quot.sound.

## Logarithm-scaled triple budget

The rank-relocation proof now accepts the explicit hypothesis

    4 fiber(A,T,n,z).card + 6 <= epsilon log N

for z<=N^33 and z!=n, in place of a constant triple cap R. The threshold
is independent of the actual host and of T. The separate far-tail bound
still requires 6<=epsilon log N; this condition is included in the eventual
threshold rather than being incorrectly inferred at a distant target.

SublogDownwardClippingExplore applies this budget to the eligible central
clipping set. The exact original brackets and the same one-target upper and
lower bounds survive. At every other natural target the absolute change is
at most epsilon log(z+2).

## Uniformity over all bracket-preserving subsets of one host

Main result:

    Erdos66SublogHostClipping.host_eventually_uniform_downward_clipping

Assume H has a K+C log(n+2) representation envelope, SmallBoundary, and
SublogCentral. H need not itself have exact brackets. For every c,epsilon>0,
there is a threshold such that for every later n and EVERY B subset H that
has the original exact harmonic brackets, one finite swap at n:

* preserves those brackets;
* is supported in [n/5,2n];
* leaves r(n) between min(old r(n),floor(c log n)-1) and floor(c log n);
* changes every other count by at most epsilon log(z+2).

The threshold is chosen before B. It uses the quantitative bounds of H,
not separately chosen eventual thresholds for each B.

For the boundary margin, SmallBoundary at tolerance c/8 combines with
log(n+2)<=2log n and c log n>=12. For the triple budget, choose cutoff d
from the boundary condition, put T=floor(n/d^2), and use SublogCentral with
comparability 2d^2, horizon 34, and tolerance epsilon/16. Eventually
n<=2d^2*T and N^33<=T^34 for N=ceil(n/5). Also log(T+2)<=2log N.
These estimates give the precise real triple budget needed by relocation.

## One uniformly clippable sparse restoration menu

Main result:

    Erdos66ClippableSparseRestorationMenu.
      exists_uniformly_clippable_sparse_restoration_menu

Assume A has exact brackets, a logarithmic envelope, SmallBoundary,
SublogCentral, and D subset A has negligible counting mass relative to
sqrt(N log N). One F disjoint from A and one N0 are selected. The FULL
insertion A union F has sublogarithmic representation increment. Every
E subset D supported above N0 has an exact-bracket restoration B_E using F.

For every c,epsilon>0, eventually in n, EVERY such E admits one-target
clipping of B_E at n with the preceding bounds. The same n threshold works
for every E. The proof uses the common envelope and qualitative invariants
of A union F, which contains every B_E.

The supporting envelope_of_sublog_change lemma upgrades the old K+C log
bound to some KB+(C+1) log bound after a sublogarithmic perturbation.

## Exact remaining limitation

This closes a moving-host threshold issue for all members of ONE preselected
sparse restoration menu. It is not a simultaneous clipping theorem for all
centers. The new clipping insertions need not belong to the common host
A union F, so the output of a clipping swap is not known to be another
member of this menu. No such closure assertion has been made.

More fundamentally, no negligible master deletion set that corrects all
upper exceptions is available, no aggregate collateral estimate for dense
exceptional centers is available, and no all-target lower repair is available.
The existing density-one and weak power-saving estimates do not imply any
of these missing properties. The finite-template review also supplied no
changing-period, cutoff-independent feasibility theorem.

No completed proof for Spec.lean has been obtained or submitted.
