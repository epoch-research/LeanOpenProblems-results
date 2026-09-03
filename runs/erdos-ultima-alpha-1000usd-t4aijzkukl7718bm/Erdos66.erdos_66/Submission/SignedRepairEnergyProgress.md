# Aggregate quadratic cost of unrestricted signed repair

## Original conjecture status

The conjecture in Submission/Spec.lean remains unresolved. The file is
unchanged with its original sorry and SHA256

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

No proof or disproof has been submitted.

## New verified files

* SignedRepairEnergyExplore.lean
* SignedRepairEnergyStabilityExplore.lean
* CompletionIncidenceEnergyExplore.lean

All three compile with current oleans and no warnings. SignedRepairEnergyAudit.lean
audits fourteen principal declarations; SignedRepairEnergyAudit.log reports
only propext, Classical.choice, and Quot.sound. None of the production files
contains a sorry or a new axiom. SignedEnergyChecks.lean is an API-search
scratch file and intentionally contains failed checks.

## 1. Exact finite quadratic budget

For finite A,B and target set T, let F=B\A, D=A\B, q=|F|+|D|,
and K(x)=degree(A,T,x)+degree(B,T,x). For any real center b put

    E_b = sum_(x in F) (K(x)-b)^2 + sum_(x in D) (K(x)-b)^2.

The exact signed identity and Cauchy--Schwarz on the disjoint sum of F,D give

    [sum_T(r_B-r_A) - b(|B|-|A|)]^2 <= q E_b.

The factor is exactly the number of changed points, not twice that number.
All new/new and deleted/deleted contributions occur through the midpoint
field; there are no restrictions on point reuse, monotonicity, or exchange
size.

For L,R>0 and nonempty T define

    Q = R E_b/(|T| L)^2,       b = beta |T| L/R.

The checked normalizedEnergy_eq also writes this as

    Q = (1/R) sum_(changed x) [R K(x)/(|T| L)-beta]^2.

If every target gains at least delta L, then

    delta <= beta(|B|-|A|)/R + sqrt((q/R) Q).

This is the new normalized_gain_energy_budget. It replaces a pointwise
maximum-contrast hypothesis by the actual aggregate squared contrast.

## 2. Limiting signed-repair consequences

Suppose |A_k|/R_k and |B_k|/R_k both tend to a.

* If q_k/R_k tends to d, Q_k tends to e, and the target sets are eventually
  nonempty with gains delta L_k, delta>0, then delta^2 <= d e.
* Without a limit for q_k/R_k, the weaker conclusion delta^2 <= 2 a e
  follows from q_k <= |A_k|+|B_k|.
* If Q_k tends to zero, any target sets enjoying those gains are eventually
  empty. Arbitrary full replacement of the original set is still allowed.
* If q_k/R_k tends to zero, then for EVERY real M, eventually k,

      T_k nonempty => Q_k > M.

  No limit of Q is assumed. This last statement gives unbounded aggregate
  energy rather than merely a large contrast at one point.

## 3. Infinite natural sets and hypothetical completions

Exact cutoff locality transfers the statements to arbitrary A,B subset Nat.
For a monotone completion A subset B with the same counting profile,
q_N=count(B\A,N), so q_N/R_N tends to zero automatically.

The logarithmic specialization uses

    R_N=sqrt(N log N), L_N=log N,
    a=2 sqrt(c/pi).

Only B's counting profile is inferred from its hypothesized nonzero
logarithmic representation limit. The same profile for the base A remains
an explicit hypothesis.

Main endpoints:

* same_coefficient_completion_energy_unbounded
* same_coefficient_completion_frequent_energy

They say that along persistent deficit target sets this normalized midpoint
energy must exceed every fixed bound, for every fixed center beta. No
old-set or completed-set degree regularity assumption is required for this
necessary conclusion.

## 4. Application gap and consistency checks

There is no established upper bound on Q for the actual exceptional target
sets of the constructed base and an arbitrary hypothetical completion B.
The field K depends on both A and B. The recently proved uniform residue
energy is a DIFFERENT quadratic expression; it does not furnish this
missing upper bound. In particular, uniformity over moduli does not turn
an arbitrary exceptional set into a residue class.

Individual triple-sparsity bounds also do not provide the needed aggregate
cancellation after summing over all target pairs. They must not be inserted
as an unproved regularity hypothesis.

Unbounded Q is compatible with sparse one-target packets, which can
concentrate their new/new sums on a tiny target set despite negligible
counting mass. Thus the necessary energy growth is not itself a
contradiction, and does not eliminate the existing positive weighted-deficit
completion theorem.

A review of global signed corrections and changing algebraic templates
produced no sufficient repair scheme, regenerated compatibility invariant,
or cutoff-independent finite-prefix construction. The two requirements of
the sharp completion criterion remain unavailable: the correct all-target
upper coefficient and sufficiently small fixed-tolerance deficit costs.
