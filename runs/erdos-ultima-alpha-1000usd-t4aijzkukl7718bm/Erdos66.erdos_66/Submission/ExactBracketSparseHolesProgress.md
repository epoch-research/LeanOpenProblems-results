# Sparse central surgery with exact harmonic brackets

## Original conjecture status

The original existential conjecture is still neither proved nor disproved.
Submission/Spec.lean is unchanged and retains its original sorry. Its SHA256
is 32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0.
An earlier submission of the unchanged file was rejected. No valid main
proof or exact-negation theorem has been obtained.

## Verified production files

1. RemoteCentralDeletionExplore.lean
2. SquareExponentScheduleExplore.lean
3. SparseCentralDeletionExplore.lean
4. ExactBracketCentralSurgeryExplore.lean
5. SparseMaskedPerturbationExplore.lean
6. ExactBracketSparseHolesExplore.lean

All six compile with current oleans and no warnings. CentralSurgeryAudit.lean
audits all 17 theorem/lemma declarations. Its saved log lists only propext,
Classical.choice, and Quot.sound.

The previous two-file uniform restoration menu is also audited now; see
UniformSparseRestorationMenuProgress.md and its seven-declaration audit.

## Main conditional surgery theorem

Erdos66ExactBracketCentralSurgery.exists_central_surgery takes the same
exact-bracket host with a global K+34 log(n+2) upper envelope, boundary
certificates, and central-triple certificates. It produces ONE set B and
a strictly increasing sequence k with k(j)>=(j+1)^2 such that:

* B satisfies EVERY original harmonic floor/ceiling prefix bracket.
* r_B(2^k(j))/log(2^k(j)) tends to zero.
* The signed error (r_B(n)-r_A(n))/log n, set to zero on the chosen center
  set, tends to zero at all natural targets.
* B has a global upper envelope KB+35 log(n+2), with KB>=0.

These are normalized holes, not assertions that the integer counts are
literally zero. Sparse restoration may add unbounded sublogarithmic counts
at the centers.

## Deletion construction

For a boundary parameter d>=2 and sufficiently large center n, delete
upperEndpoints(A,floor(n/d^2),n). Its residual count at n is at most
2*boundary(A,d,n).card+1.

For EVERY other target z, the packet has at most max(tripleCap(66),3)
old-partner hits. To prove this uniform bound, write T=floor(n/d^2).
For large n, n<=2d^2*T and n<=T^2. The host triple certificate with horizon
exponent 66 covers z<=n^33. The checked short-support tail theorem covers
all z>n^33. The resulting bound is independent of d; only the threshold
for n depends on d.

Choose centers 2^k(j) far enough out for the j-th boundary certificate and
the preceding packet bound. The exponent schedule also satisfies
k(j)>=(j+1)^2. At any natural target z, all relevant packets occur among
fewer than 1+sqrt(log_2(2(z+1))) indices. This is o(log z), so their bounded
collateral sums to o(log z) away from the centers.

The entire deletion set lies in the old dyadic-deletion set. Its counting
mass is therefore o(sqrt(N log N)) by the existing dyadic deletion theorem.
The simultaneous sparse rank restoration theorem applies ONCE to this
whole deletion set. It retains all brackets and adds only o(log n) at all
targets. No sum of stagewise logarithmic restoration errors is used.

## Unconditional counterexample to auxiliary sufficiency

Erdos66ExactBracketSparseHoles.exists_exact_brackets_and_sparse_holes
starts with the jointly constructed exact-bracket host. Its single set B
has all of the following:

* Exact harmonic prefix brackets at every cutoff.
* A global KB+35 log(n+2) representation upper bound.
* Coefficient-one convergence outside one harmonically summable,
  density-zero exceptional set E.
* For every fixed epsilon>0, some positive alpha<1 such that the bad
  epsilon-targets have summable (n+2)^(-1+alpha) weight and their count
  divided by (N+2)^(1-alpha) tends to zero.
* Normalized representation counts tending to zero on a strictly increasing
  sparse dyadic sequence.
* No finite pointwise normalized representation limit whatsoever.

The power-exception transfer is proved for arbitrary real sequences and
signed masked perturbations; it does not assume monotone insertion.

## Exact scope

This result does NOT disprove the original existential conjecture: it
constructs one bad set, not an obstruction to all sets. It shows that exact
brackets combined with the listed upper and exceptional-count estimates
still do not suffice to conclude pointwise convergence.

The output is NOT asserted to retain the original summable powerCost rows,
central-triple caps, or exact numerical boundary certificates. The qualitative
power-saving exceptional estimates are proved separately by the signed
perturbation transfer. Those properties must not be conflated.

## Remaining main gap

No negligible master correction set for all upper/lower exceptions has
been produced. No compatible changing-field all-prefix construction,
uniform sublogarithmic Boolean self-convolution rounding, or universal
logarithmic-order fluctuation obstruction has been found.
