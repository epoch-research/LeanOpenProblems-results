# Universal complete-partition transfer for all later coarse kernels

## Original task status

The conjecture in Submission/Spec.lean is still neither proved nor disproved.
Its original import, statement, and sorry remain unchanged. No proof has
been submitted. None of the results below settles the original existential
natural-number statement.

## New result: remove the finite coarse-target budget

Fix an odd finite field F of size n, an equivalence rho:Fin n~F, and a
finite nonempty color alphabet alpha. A SINGLE coloring

    omega:Fin n -> alpha

is selected before ALL of the following:

* the later real pair kernel K, with no symmetry assumption;
* the later graph f:F->F and its sum-fiber bound D;
* every fine target (t,s);
* arbitrary finite or infinite coarse families B,C;
* all coarse targets, without a finite target list or a weighted budget;
* arbitrary later finite graph patches, for the patch version.

Vertical translates of f form a complete disjoint partition of F^2.
Their actual weighted representation sum obeys

    [graphSum(K;t,s)-n^2 mean(K)]^2
      <= D^2 n (8n^2+2n) sum_(a,b) [K(a,b)-mean(K)]^2.

The unnormalized centered matrix norm is retained. There is no hidden
factor depending on the number of coarse targets.

## Symmetrization and the matrix basis

KernelSymmetrizationExplore.lean removes the symmetry hypothesis from the
existing expected color-energy bound. Transposition leaves every label-sum
fiber unchanged, so symmetrizing K leaves its color energy unchanged. It
preserves the mean and centered diagonal second moment and contracts the
variance. Thus the old expectation bound applies to ANY real K.

CompleteKernelBasisExplore.lean uses ordered indicator masks

    M_ab(x,y)=1_((x,y)=(a,b)).

Writing Q=|alpha|^2, their exact pointwise centered mass is

    sum_(a,b) [M_ab(x,y)-1/Q]^2 = 1-1/Q <=1.

Averaging gives both

    sum_(a,b) variance(M_ab)<=1,
    sum_(a,b) diagonalCenteredSecond(M_ab)<=1.

Consequently one coloring has total mask color energy <=8n^2+2n, independently
of |alpha|. Reconstruct any later kernel in the mask basis and apply
Cauchy--Schwarz in each label-sum fiber. Applying this to the centered
kernel gives

    colorEnergy(K) <= (8n^2+2n) sum_(a,b) [K(a,b)-mean(K)]^2.

Constant kernels have zero error exactly. The color dimension is still
present in the unnormalized matrix norm; this is not dimension-free
relative accuracy for arbitrary growing alphabets.

## Actual mixed counts, including infinite coarse sets

UniversalCompleteGraphExplore.lean checks the finite mixed assembly identity
for B,C, not just self-counts. Members within and across B,C may overlap.
Only the fine graph slices must be disjoint, and they are.

For infinite B,C:alpha->Set Nat, infiniteGraphSet is the genuine union of
fine graph slices times the nonnegative integer supports of their assigned
coarse sets. The representation count is the cardinality of actual first
endpoints. The already checked locality theorem truncates at each target
only within the proof, so no cutoff is chosen before the coarse data.
The same universal centered bound holds for every natural coarse target.

Exact prefix causality is also proved for a FIXED graph, field, and coloring.
It is not a theorem comparing different fields or different operators.

## Relative accuracy and color cost

UniversalCompleteAccuracyExplore.lean proves

    centeredMass(K)=|alpha|^2 variance(K).

For nonnegative K,

    centeredMass(K)<=|alpha|^4 mean(K)^2.

For n>=1, the explicit sufficient condition

    10 D^2 |alpha|^4 <= epsilon^2 n

therefore gives

    |error| <= epsilon n^2 mean(K).

This includes mean zero. One coloring is selected even before epsilon;
all later requests satisfying the displayed numerical condition are covered.
The same statement is proved for actual infinite mixed assemblies.

Unlike the earlier sparse-curve universal palette, the graph slices form
a COMPLETE partition. The exact infinite membership rule is

    ((x,y),q) in infiniteGraphSet
      iff q in natSupport(B_(omega(rho^-1(y-f(x))))).

If every coarse color is nonempty, the fine projection is all of F^2.
This is not being confused with asymptotic residue equidistribution.

## Later patches

If f has sum-fiber bound D and g differs from f only on T, the same
universal matrix selection gives

    error(g,K)^2
      <= (2 D^2 n+32|T|^2)(8n^2+2n) centeredMass(K).

The patched graph need not have a separately supplied degree/fiber bound.
There is also a checked actual infinite mixed-count version. The finite
patch remains a prescription of graph columns, not an arbitrary Boolean
prefix of a natural-number construction.

## Principal declarations

Erdos66CompleteKernelBasis.exists_universal_centered_energy
Erdos66UniversalCompleteGraph.exists_universal_graph_kernels
Erdos66UniversalCompleteGraph.exists_universal_patched_kernels
Erdos66UniversalCompleteGraph.exists_universal_actual_mixed
Erdos66UniversalCompleteGraph.exists_universal_infinite_mixed
Erdos66UniversalCompleteGraph.exists_universal_infinite_patched
Erdos66UniversalCompleteAccuracy.exists_universal_graph_accuracy
Erdos66UniversalCompleteAccuracy.exists_universal_infinite_accuracy

## Verification

Four production files compile with current oleans:

* KernelSymmetrizationExplore.lean
* CompleteKernelBasisExplore.lean
* UniversalCompleteGraphExplore.lean
* UniversalCompleteAccuracyExplore.lean

UniversalCompleteAudit.lean audits 35 principal declarations; its saved log
uses only propext, Classical.choice, and Quot.sound. The sources have no
sorry or new axiom. A few unused-section-variable warnings are harmless.

## Remaining mathematical gap

It is NO LONGER correct to say that complete-partition transfer intrinsically
requires a finite list of coarse targets. That limitation has been removed,
at the displayed centered-norm/color-dimension cost.

The result does not create an accurate coarse main term. It also does not
supply an improving-precision colored invariant through successive stages,
an integer carry estimate across changing fine moduli, or simultaneous
control of all intermediate natural-number prefixes.

For a kernel of mean mu, variance of order mu, and target mean M=n^2 mu,
the available universal relative squared bound is of order

    D^2 |alpha|^2 n/M.

This is the universal bound's extra color-dimension cost, not the old
single-kernel n/M estimate. It cannot be discarded when the alphabet grows.
Using only nonnegativity retains the fourth-power condition above.

The elementary density bookkeeping also matters: giving every fine point
one coarse color does not itself dilute an arbitrary coarse source to the
required natural density. A source with the correct main profile, or a
compatible construction of such sources, is still needed. No such source
or compatible changing-scale iteration has been obtained here.

## Subsequent ordinary-carry transfer

The complete partition now has a checked fixed-field natural-number
transfer, including both carry levels and full fine coverage. See
UniversalCompleteCarryProgress.md. It retains the explicit alphabet cost
and coarse integer-weight profile; changing-scale compatibility and an
infinite witness remain unproved.
