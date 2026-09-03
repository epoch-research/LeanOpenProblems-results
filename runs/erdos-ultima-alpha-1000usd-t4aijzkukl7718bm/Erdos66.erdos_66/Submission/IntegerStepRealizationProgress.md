# Actual finite integer realization of bounded step profiles

## Original task status

The conjecture in Submission/Spec.lean remains unresolved. Its statement,
import, and original sorry are unchanged. No proof has been submitted.

## Exact interval slicing

IntegerPaletteSlicesExplore.lean defines

    slice(M,C,a,b) = {z.val : z in C, a<=z.val<b}.

For two such pieces, set

    hi = min(b,n+1-c),
    lo = min(max(a,n+1-d),hi).

When d<=M, the exact mixed INTEGER pair count is

    pairs(slice(C,a,b),slice(D,c,d),n)
      = intervalCount(M,C,D,n mod M,lo,hi).

The clamped endpoints correctly handle empty intersections and all integer
carries. If b,d<=M and all endpoint-prefix errors are at most eta times the
actual mixed mean, the integer mixed count differs from

    ((hi-lo)/M) actualMean(M,C,D)

by at most 2 eta actualMean(M,C,D), uniformly in every natural target n.

## Piecewise assembly and its two errors

IntegerPaletteAssemblyExplore.lean assembles C_i on disjoint intervals
[a_i,b_i) inside [0,M). Its exact representation count is the double sum of
the mixed integer counts of its pieces. Write

    overlap_ij(n) = (hi_ij(n)-lo_ij(n))/M,
    profile(n) = sum_ij overlap_ij(n) actualMean(M,C_i,C_j).

Then at EVERY natural n,

    |r_A(n)-profile(n)| <= (2 eta/M) (sum_i |C_i|)^2.

No monotonicity of the spatial choices is needed. The same assembly also
has its expected total cardinality, with error <=2 eta sum_i |C_i|, when
prefix control against the full palette member is included.

IntegerPaletteQuantizationExplore.lean fixes nonnegative weights w_i and
selects members with

    w_i |B| <= |C_i| <= R w_i |B|,   R>=1.

For mu=actualMean(M,B,B) and

    F(n)=sum_ij overlap_ij(n) w_i w_j,

it proves

    |r_A(n)-mu F(n)|
      <= [(1+2 eta) R^2-1] mu (sum_i w_i)^2.

This separates the spatial mixed-count error from the cardinality-level
quantization error. Complete-palette coverage chooses all the C_i in the
SAME palette whenever w_i>=1 and w_i|B|<=M.

## Unconditional logarithmic step realization

LogarithmicStepRealizationExplore.lean proves

    Erdos66LogarithmicStepRealization.exists_logarithmic_step_realization.

Fix any finite index set, fixed real heights w_i>=1, c>0, delta>0, and N0.
There is M>N0, M>1, such that AFTER M is chosen, ANY pairwise disjoint
intervals [a_i,b_i) inside [0,M) admit an actual finite A subset [0,M) with

    |r_A(n)/log M - c F(n)| <= delta

for EVERY natural target n. Empty intervals are allowed. The bound does
not depend on the interval endpoints or on the target.

The proof uses the spatially balanced complete palette with precision

    t = min(1, delta/[100(c+1)((sum_i w_i)^2+1)]).

Its actual sparse mean is tuned close to c log M. A log(M)/M -> 0 bound
ensures every fixed height fits below full cardinality. Finally,

    0 <= (1+2t)(1+t)^2-1 <= 11t

and the mean-tuning error give the asserted normalized estimate.

## Verification

All four production files compile and have built oleans:

* IntegerPaletteSlicesExplore.lean
* IntegerPaletteAssemblyExplore.lean
* IntegerPaletteQuantizationExplore.lean
* LogarithmicStepRealizationExplore.lean

IntegerStepRealizationAudit.lean checks their principal declarations. Only
propext, Classical.choice, and Quot.sound occur. The production files have
no sorries or new axioms. PaletteAssemblyChecks.lean is a name-search scratch
file, not a production dependency; it contains one intentionally failed check.

## Remaining gap

These are ACTUAL integer sets, not just cyclic counts, and arbitrary fixed
bounded step profiles can now be transferred without assuming root-location
equidistribution. But the finite number and heights of the steps must be
fixed BEFORE choosing the modulus. The precision and the modulus threshold
depend on them.

In particular, this does not cover an inverse-square-root density profile
uniformly all the way down to a fixed natural cutoff as M grows. Doing so
requires an increasing number or range of levels, or another multiscale
argument. Nor does this preserve an earlier integer set while changing M.
The cutoff-independent finite-prefix feasibility needed by compactness is
still unproved. No universal contradiction to the conjecture was obtained.
