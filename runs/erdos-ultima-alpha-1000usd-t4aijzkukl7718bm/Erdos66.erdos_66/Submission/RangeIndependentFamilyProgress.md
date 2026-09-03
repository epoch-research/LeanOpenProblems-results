# Range-independent finite mixed families

## Original conjecture status

The conjecture in `Submission/Spec.lean` remains unproved and undisproved.
The file is unchanged, and no proof has been submitted. None of the finite
results below is being asserted as an infinite natural-number construction.

## New asymmetric energy estimate

`AsymmetricMixedEnergyExplore.lean` proves, on a finite abelian group,

    energy(f,g)^2 <= M^2 |S| energy(f,f),

when corr(f) is supported on S and |corr(g)(t)|<=M everywhere.
It follows from energy(f,g)=sum corr(f)corr(g), the trivial bound for g,
and Cauchy--Schwarz on the support of corr(f).

For signed quadratic-character intervals of lengths 1<=h<=k<=p,

    [sum_z |crossCharFiber(U_h,U_k,z)|]^4
      <= 12 h k^4 translatedEnergy([0,h),a).

ONLY the shorter interval's self-energy appears. In particular, if that
energy is at most w h^2 and 12w<=e^4 h, the mixed character L1 norm is at
most e h k, independently of the size of k. No Fourier theorem is required.

This avoids the loss from using two independently bounded self-energies
when the parameter lengths are very different.

## Summably weighted translate selection

`WeightedTranslateSelectionExplore.lean` chooses one admissible translation
for any finite list U_0,...,U_(N-1), with

    translatedEnergy(U_j,a) <= 16 (j+1)^2 |U_j|^2.

The constant does NOT grow with N. The normalized costs are weighted by
1/(j+1)^2, whose finite sums are at most two. The forbidden-translation
set still has to occupy less than half the field, exactly as before.

## Quadratically spaced levels

Define

    level(D,j) = D (j+1)^2.

`QuadraticLevelSelectionExplore.lean` combines weighted selection with the
asymmetric bound. If e>0, D>0, D e^4>=96 and p>8 level(D,J)+3, there is one
admissible translated parameter family such that, for EVERY i,j<=J,

    sum_z |crossCharFiber(U_(2 level(D,i)),U_(2 level(D,j)),z)|
      <= e * 4 level(D,i) level(D,j).

The key cancellation is that the selection cost (i+1)^2 is proportional to
the shorter parameter length. Thus the spacing D is independent of J.

## Actual nested finite-field sets, including the origin

`RangeIndependentFamilyExplore.lean` uses the existing banded origin repair.
For eta>0 choose natural D,g satisfying

    g>0, g<=D, D eta^4>=1536, eta g>=34.

These choices are independent of J. For EVERY J and EVERY prime

    p > max(8 level(D,J)+3, 4g level(D,J)),

there is a nested family B_i in (ZMod p)^2 with, for all i,j<=J and ALL z,

    |r_(B_i,B_j)(z)-4 level(D,i) level(D,j)|
      <= eta * 4 level(D,i) level(D,j).

Principal theorem:

    Erdos66RangeIndependentFamily.exists_range_independent_flat_family

The origin count is exactly 1+4 level(D,i) level(D,j), and its one-unit
error is included. Nonzero-target repair costs are bounded using
natural_banded_cost, with 17/g<=eta/2.

Compared with the older every-prime banded family, the spacing constant no
longer grows with the maximum index. The nominal levels are quadratic rather
than linear in the index. The field threshold is linear in the largest
actual level, with constants depending only on the precision.

## Actual cyclic transfer

`RangeIndependentCyclicExplore.lean` proves that for 0<eta<=1 there are
D,g,K0, all independent of J, such that for every prime above the displayed
threshold and every K>=K0, there are nested sets C_i modulo (pK)^2 with

    |r_(C_i,C_j)(z)-4 K^2 level(D,i) level(D,j)|
      <= eta * 4 K^2 level(D,i) level(D,j)

for every i,j<=J and every cyclic target. This uses the already checked
mixed carry-transfer theorem, not an assumed relation-preserving embedding.

## Scalar multiplicative coverage

`QuadraticLevelCoverageExplore.lean` proves that for every epsilon>0 there
is an initial index I, independent of D and J, such that every real x in

    [level(D,I), level(D,J)]

is bracketed by some level(D,j), I<=j<=J, with

    x <= level(D,j) <= (1+epsilon)x.

This is a theorem about NOMINAL scalar levels. An actual-cardinality palette
coverage theorem has not yet been derived in this continuation.

## Verification

All six new production files compile and have oleans. Principal results
are audited in:

* RangeIndependentAudit.lean
* RangeIndependentCyclicAudit.lean

Only propext, Classical.choice, and Quot.sound occur. The production files
contain no sorries or new axioms. AsymmetricChecks.lean is only a name-search
scratch file and includes a failed check; it is not a production dependency.

## Remaining infinite problem and possible next finite step

This improvement is still within ONE finite field or ONE cyclic modulus.
It does not control mixed counts between unrelated periods, preserve an
already accurate natural-number prefix, or fill the intermediate scales.
The previous literal-radix gaps and repeated-copy obstructions remain valid.

A useful next finite step is actual-cardinality coverage, followed by a
complete palette whose coverage begins at a logarithmic sparse member.
For a sufficiently late initial index, adjacent quadratic nominal levels
have ratio arbitrarily close to one. Self-count bounds control the actual
cardinality means, and the existing dense completion can then be attached
at a larger member. This requires a proof and has NOT been inferred here.

Caution: an analogous low-level coverage improvement may already be
obtainable from the older linear-index families by beginning at a large
fixed index I and tuning the mean at C_I rather than C_1. The previously
reported coverage starting at C_H is a limitation of that theorem's
statement, not a universal impossibility of sparse-start coverage. Literal
dense-member placement still has its genuine mass cost, regardless of how
a finite palette is indexed.

No conclusion resolving `Spec.lean` has been obtained.

## Subsequent update

Actual-cardinality coverage and logarithmic sparse-start completion have now
been checked via the older linear-index family, as anticipated above. See
SparseStartPaletteProgress.md. PrefixBalancedPaletteProgress.md adds uniform
mixed endpoint-prefix control by outer repetition. These are still finite
same-modulus statements; the infinite compatibility gap remains.
