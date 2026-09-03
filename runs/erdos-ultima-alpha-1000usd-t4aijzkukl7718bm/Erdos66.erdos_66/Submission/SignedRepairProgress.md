# Unrestricted signed repair accounting and incidence contrast

## Original task status

The conjecture in Submission/Spec.lean remains unresolved. Its import,
statement, and original sorry are unchanged. No proof or disproof has been
submitted. SHA256:

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## Verified production files

* SignedRepairIncidenceExplore.lean
* SignedRepairStabilityExplore.lean

Both compile with current oleans. SignedRepairAudit.lean audits eleven
principal declarations; SignedRepairAudit.log reports only propext,
Classical.choice, and Quot.sound. No production placeholders or axioms
were introduced. SignedRepair*Checks*.lean files are API scratch files.

## Exact signed identity

For finite A,B and target set T, let

    F = B minus A,    D = A minus B,
    degree(S,T,x) = #{s in S : x+s in T},
    K(x) = degree(A,T,x)+degree(B,T,x).

The checked midpointDegree_union_inter identity also writes K as

    degree(A union B,T,x)+degree(A intersect B,T,x).

The exact signed accounting is

    sum_(n in T) [r_B(n)-r_A(n)]
      = sum_(x in F) K(x) - sum_(x in D) K(x).

Every new/new, deleted/deleted, and common-point contribution is retained.
For any real b, centering gives

    sum_T [r_B-r_A] - b(|B|-|A|)
      = sum_F (K-b) - sum_D (K-b).

Consequently, if |K(x)-b|<=epsilon on all changed points, its absolute value
is at most epsilon (|F|+|D|). The signed change in cardinality, rather than
the full number of edits, occurs in the centered main term.

## Scaled repair budget

Let L,R>0, eta>=0, and suppose T is nonempty. If every n in T gains at least
delta L and every changed point obeys

    |R K(x)-beta |T| L| <= eta |T| L,

then

    delta R <= beta(|B|-|A|)+eta(|A|+|B|).

Principal finite theorem:

    Erdos66SignedRepairIncidence.normalized_signed_budget.

There is no monotonicity, point-reuse, packet-shape, or small-symmetric-
difference assumption.

## Infinite density-preserving edits

Suppose both counting functions divided by R(N) tend to the same a. For
fixed eta>=0 with 2 a eta<delta, the displayed degree regularity and uniform
gain imply that T_N is eventually empty. This follows by dividing the finite
budget by R: its right side tends to 2 a eta, while its left side is delta.

Exact cutoff locality transfers the result to arbitrary infinite sets A,B.
They can differ at infinitely many points in both directions, and can replace
an unrestricted fraction of their points.

Conversely, persistent nonempty target sets with gains delta L force a
positive incidence contrast. The theorem chooses

    eta = delta / [4(|a|+1)] > 0.

For every fixed beta, arbitrarily large N then have a changed point x<N with

    |R(N) K_N(x)-beta |T_N| L(N)| > eta |T_N| L(N).

Main names, namespace Erdos66SignedRepairStability:

* same_mass_regular_edits_empty
* same_counting_regular_edits_empty
* same_counting_frequent_contrast
* same_coefficient_frequent_contrast

The last specializes R(N)=sqrt(N log N), L(N)=log N, and uses the checked
Tauberian counting profile of a hypothetical logarithmic-limit completion B.
The base A is explicitly required to have that same counting profile; it is
not silently inferred from a bare density-one representation limit.

## Application review and remaining gap

The old monotone incidence theorem required arbitrarily large normalized
new-point degrees when the addition has negligible counting mass. The new
signed theorem permits deletion and full replacement: it instead requires
a fixed positive contrast from any proposed constant midpoint degree.
Neither conclusion is a contradiction by itself.

The existing local-difference and triple-sparsity estimates do NOT establish
the degree regularity used here for the actual exceptional target sets. A
bound for each individual triple intersection does not control its sum over
a dense family of exceptional centers. Moreover K_N depends on the proposed
completion B as well as on the constructed base A. Bounds on A alone cannot
silently replace this midpoint field.

Thus the review has not supplied a coordinated signed repair, a correct
all-target upper coefficient, or the deficit-weight summability needed by
the existing completion theorem. The positive power saving at each fixed
tolerance remains insufficient for that completion criterion. No new
compatible finite-prefix construction or universal logarithmic-scale
contradiction has been obtained.
