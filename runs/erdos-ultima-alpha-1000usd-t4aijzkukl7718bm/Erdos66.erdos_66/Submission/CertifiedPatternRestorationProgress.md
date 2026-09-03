# Qualitative pattern invariants and a certified sparse restoration menu

## Original task status

The conjecture in `Submission/Spec.lean` remains unproved and undisproved.
Its original import, statement, and `sorry` are unchanged. The results here
are auxiliary and are not a valid submission settling the conjecture.

## Verified files

* DifferenceNaturalPatternExplore.lean
* JointDifferencePatternHostExplore.lean
* TranslatedDifferencePatternExplore.lean
* JointTranslatedDifferenceHostExplore.lean
* PatternInsertionDominationExplore.lean
* SublogPatternInvariantsExplore.lean
* CertifiedSparseRestorationMenuExplore.lean

All seven compile and have current oleans. `CertifiedPatternRestorationAudit.lean`
audits all 46 theorem/lemma declarations; its saved log reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Joint difference host

The first four files extend the original boundary/triple host with two
families of matching tests, without changing the original encoding tags.
One host simultaneously retains exact harmonic prefix brackets, a global
K+34 log(n+2) envelope, all original power-cost rows, the original boundary
certificates, the original constant central-triple caps, and:

* eventually localDiff(A,N,d) <= 144 log(N+1), for all d>0;
* eventually translatedDiff(A,N,d) <= 16(8(h+1)+1) log(N+1),
  uniformly in h and 0<d<=N^h.

Here localDiff requires both endpoints in [N,2N), whereas translatedDiff
counts a in [N,2N) with a,a+d in A and has no window condition on a+d.
These are genuinely joint properties of one selected host.

## Pair-increment domination

For A subset B, let delta(n)=r_B(n)-r_A(n). The verified estimates are

    boundary(B,d,n).card <= boundary(A,d,n).card + delta(n),
    fiber(B,N,n,z).card <= fiber(A,N,n,z).card + delta(n)+delta(z).

A new triple has a new pair at at least one of its two targets. A nonempty
central fiber forces both targets to be at least N.

## Two preserved qualitative properties

SmallBoundary(A): for every epsilon>0 there is d>=2 such that eventually

    boundary(A,d,n).card <= epsilon log(n+2).

SublogCentral(A): for every fixed C,h and epsilon>0, eventually in N,
uniformly for n<=CN, z<=N^h, and n!=z,

    fiber(A,N,n,z).card <= epsilon log(N+2).

Both properties follow from the original stronger certificates. Both are
downward hereditary. Both are preserved under A subset B when

    (r_B(n)-r_A(n))/log(n+2) -> 0.

The triple proof uses the uniform polynomial-window consequence of a
sublogarithmic sequence, not a pointwise limit with a moving threshold.
It does NOT assert preservation of the original constant triple caps.

## Certified menu

`Erdos66CertifiedSparseRestorationMenu.exists_certified_sparse_restoration_menu`
assumes exact harmonic brackets, the two qualitative properties, D subset A,
and count(D,N)/sqrt(N log N) -> 0. It chooses ONE F disjoint from A such that:

* for every later E (without a remoteness restriction), restoredFrom(A,F,E)
  has SmallBoundary and SublogCentral;
* for every epsilon>0 there is a cutoff N such that every E subset D supported
  above N has an exact-bracket restoration using this same F;
* the insertion above A minus E is globally between zero and epsilon log(n+2),
  and its normalized limit is zero.

The invariants hold because the full insertion A union F has sublogarithmic
representation increment, and every restored set is a subset of A union F.
The insertion comparison is with the DELETED CORE, not with the original A.

## Review of downward clipping and the unresolved step

In FlexibleRankDownwardRepairExplore.lean, the fixed triple cap R is used
only through the eventual inequality 4R+6 <= epsilon log N. A corresponding
uniform sublogarithmic triple estimate can replace that use mathematically;
no new generalized clipping theorem has been formalized in this pass.

This still addresses only local repairs. There is no proved negligible
master deletion set clipping all upper exceptions, and no compatible repair
of all lower exceptions. Accumulated collateral across dense exceptional
target sets and thresholds across changing hosts remain uncontrolled.
The new invariants and menu do not supply either missing construction.
