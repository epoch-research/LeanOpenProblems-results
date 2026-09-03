# Automatic cores cannot supply the mass of a witness

The original conjecture remains unproved and undisproved. Spec.lean is
unchanged. This result is not a disproof of its existential statement.

## New checked result

`AutomaticCoreExplore.lean`, namespace `Erdos66AutomaticCore`, strengthens
the finite-state obstruction to automatic subsets of a hypothetical witness.

Suppose A has a nonzero finite logarithmic representation limit, and B is
an automatic subset of A, recognized in a base b>=2 with zero padding.
Then, at EVERY natural cutoff N tending to infinity,

    count B N / count A N -> 0,
    count (A minus B) N / count A N -> 1.

In particular, if A=B union D, then

    count D N / count A N -> 1.

Thus an automatic core cannot be turned into a witness by adjoining a set
negligible relative to the result. This is stronger than merely excluding
an automatic witness or a finite modification of one.

## Proof

The digit-loop theorem applies to every automatic subset of A, because
its digit cubes would also give representation peaks in A. Hence the
loop-unique automaton bound gives

    count B (b^k) <= ((k+1)*(b+1))^S.

Comparison with the adjacent base powers, using k=floor(log_b N), proves

    (count B N)^2/N -> 0

at all cutoffs. On the other hand, eventual-basis status gives

    N <= M+(count A N)^2.

The squared ratio is squeezed to zero, and continuity of square root
recovers the ratio itself. Finite-set difference and union inequalities
give the complement and augmentation conclusions.

## Main declarations

- count_sq_div_zero_of_poly_bound
- negligible_relative_to_basis
- automatic_subset_negligible
- automatic_complement_full
- automatic_union_repair_full
- no_negligible_automatic_repair

The production file compiles and has a built olean. The six principal
results are checked in AutomaticCoreAxiomCheck.lean; only propext,
Classical.choice, and Quot.sound occur.

## Main unresolved issue

No automatic-core hypothesis appears in the conjecture. A prospective
witness may have genuinely unbounded-memory structure throughout almost
all its counting mass. This theorem neither constructs such a set nor
excludes it. Mixed counts through compatible near-scale transitions
remain uncontrolled.
