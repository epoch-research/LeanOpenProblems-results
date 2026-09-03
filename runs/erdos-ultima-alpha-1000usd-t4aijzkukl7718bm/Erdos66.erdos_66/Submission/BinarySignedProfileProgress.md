# Binary scalar profiles with logarithmic-square coarse exceptions

## Original task status

The conjecture in `Spec.lean` is still neither proved nor disproved.
Its original statement and `sorry` are unchanged. No solution has been
submitted.

## Checked production files

1. `RealWeightedCharacterEnergyExplore.lean`
2. `WeightedProfileCharacterExplore.lean`
3. `SignedRepBernoulliExplore.lean`
4. `BinarySignedProfileExplore.lean`
5. `BinaryAggregateBlocksExplore.lean`

All compile with built oleans. `BinarySignedProfileAxiomCheck.lean` audits
the main results; only propext, Classical.choice, and Quot.sound occur.

## 1. Weighted character energy

For real weights v_i, i<h, and odd prime p>=h, write

    S_a(q) = sum_{i,j<h, i+j=q} v_i chi(a+i) v_j chi(a+j).

`average_signed_fiber_energy` proves

    sum_a S_a(q)^2 <= 4p sum_{i+j=q} (v_i v_j)^2.

`average_signed_energy` sums over q<2h to obtain

    sum_a sum_{q<2h} S_a(q)^2 <= 4p (sum_{i<h} v_i^2)^2.

The squared-weight mass is retained, rather than replaced by h. The proof
extends the elementary quadratic-character correlation identity to real
weights, bounds collision fibers of the square map by two, and uses the
same two-to-one square averaging as the earlier integer-weight theorem.
No higher-degree Weil estimate is assumed.

For p>4h, `exists_admissible_weighted_translate` excludes all zero/opposite
parameters and chooses one a with

    sum_{q<2h} S_a(q)^2 <= 8 (sum_{i<h} v_i^2)^2.

Consequently, for EVERY threshold E>=0, the number of q<2h with |S_a(q)|>E
satisfies

    number_bad * E^2 <= 8 (sum_{i<h} v_i^2)^2.

## 2. Shifted fractional profile

Take v_i=sqrt(mu) b(i+s), with the existing binomial profile b. Its squared
mass satisfies

    sum_{i<h} v_i^2 <= mu H_h <= mu (1+log h).

For every epsilon>0, the same admissible a therefore has at most

    8 (1+log h)^2 / epsilon^2

coarse targets where |S_a(q)|>epsilon mu. This bound is independent of mu
and of the prime size. `exists_fractional_root_profile` also connects the
bound to the affine field-plane root counts, with unsigned mean
mu*tailConv(s,q). This step alone is fractional, not a natural set.

## 3. Simultaneous unsigned and signed Bernoulli rounding

`SignedRepBernoulliExplore.lean` uses three nonnegative tests at every coarse
sum: the unsigned count and the positive and negative parts of the signed
count. All are sums of disjoint monomials with weights in [0,2]; their means
are bounded by the unsigned representation mean.

`exists_unsigned_signed_bound` obtains one binary realization with unsigned
error <delta V and signed error <2 delta V, provided

    6 (Q+1) exp(-delta^2 V/8) < 1.

The exact signed mean is the fractional signed convolution PLUS

    sum_diagonal sigma_i^2 (p_i-p_i^2),

which lies in [0,1]. It is not silently discarded. General bridge lemmas
identify the selected signed count with the label convolution of the actual
finite set, including for q beyond the support cutoff.

## 4. Actual binary coarse profile

`Erdos66BinarySignedProfile.exists_binary_signed_profile` takes:

    p odd prime, p>4(L+1),
    mu>=1, 0<epsilon<=1, epsilon mu>=8,
    mu<=s+1,
    64 s^2 <= epsilon^2(q0+1),
    6(2L+1) exp(-epsilon^2(mu+1)/512) < 1.

It produces a, finite T, and D contained in [0,L], with admissible affine
parameters, such that:

* |T| <= 128 (1+log(L+1))^2/epsilon^2;
* r_D(q) <= (1+epsilon)mu for EVERY q;
* |r_D(q)-mu| < epsilon mu for q0<=q<=L;
* the character-signed convolution of 1_D has absolute value <epsilon mu
  for EVERY q<=2L outside T.

The prime is arbitrary above its range bound; it does not occur in the
concentration budget. These are explicit finite numerical hypotheses, not
assumptions asserting a solution of the original conjecture.

## 5. Actual integer blocks outside coarse exceptions

`Erdos66BinaryAggregateBlocks.exists_aggregate_blocks` composes this binary
profile with the previously proved affine/collective integer transfer.
After coordinate thickening K and outer repetition J, the actual natural
block set has, at every fine target in a coarse block q with

    q0+1<=q<=L,  q notin T,  q-1 notin T,

representation count within

    (J+1)[K^2(2 epsilon mu)+2K(mu+2 epsilon mu)] + K^2 mu

of J K^2 mu. No pairwise flatness or dense palette members are used.

## What is still missing

T consists of COARSE TARGETS. An exceptional coarse target represents an
entire large interval of natural targets, not one sparse integer exception.
Thus the existing pointwise sparse-deficit completion theorem cannot be
applied directly. No sharp global integer upper bound has been supplied at
these exceptional blocks, and no block-repair theorem is proved here.

There is also still no compatible change of prime/period preserving an
accurate natural-number prefix. The new theorem is finite and does not
settle Erdős 66.

## Possible next test (not a proved theorem)

Choosing mu much larger than log^2 L makes |T|/mu small. A large shift s,
while keeping s^2=o(L), could force bad signed-mean targets to have large
coarse locations. This suggests deleting pairs responsible for bad blocks
and repairing those entire blocks with individually controlled curves.
Such a plan must prove uniform collateral bounds, assign nonopposite
parameters, and supply a genuine inter-scale compatibility mechanism.
None of those conclusions follows merely from the exceptional-set count.
