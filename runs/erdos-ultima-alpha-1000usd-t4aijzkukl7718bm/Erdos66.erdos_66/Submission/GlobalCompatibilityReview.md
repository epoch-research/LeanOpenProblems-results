# Global compatibility review after whole-block repair

The existential conjecture remains unresolved. The only new checked result in
this continuation is `LiteralTemplateLimitExplore.lean`; see its progress file.
The original `Spec.lean` is unchanged.

## New literal-limit check

The actual thickened, outer-repeated, unshifted integer encoding has no
positive point below its prime. This applies also to unions of nonzero-
parameter curves, not just single curves. Consequently, taking the prime to
infinity and then taking an eventual coordinatewise limit gives a subset of
{0}, rather than a candidate for the conjecture.

## Mathematical routes reviewed, with no new theorem claimed

* Joining independent finite templates still requires pointwise control of
  mixed representation counts at transitions. Making the separately checked
  self-errors smaller does not provide this.
* The finite parameter regime can make log(prime) much larger than the log of
  the coarse length. This is why a logarithmic main term can be achieved on
  a useful annulus. It does not supply a construction on an entire prefix.
* Shared-field or product-digit iterations would need both a suitable initial
  digit profile and control of accumulating product peaks. The already checked
  slice/radix and cube barriers must not be discarded in such an iteration.
* A near-scale extension is a genuine simultaneous convolution-rounding
  problem. In the first new window [N,2N), all new contributions are mixed
  with the old prefix; an arbitrary sparse packet repair is not a substitute
  for constructing the necessary macroscopic new mass.
* The existing energy lower bounds operate at square-root-logarithmic error
  scale. No amplification to a contradiction with o(log n) was established.

The current unresolved issue is still a new global compatibility/construction
principle, or a universal obstruction strong enough to negate the existential
statement. No such principle or obstruction was proved in this continuation.

## Finite-state continuation

The digit-word obstruction has now been completed and axiom-audited; see
`DfaObstructionProgress.md`. `Erdos66DfaCounting.no_nonzero_log_limit` excludes
sets recognized by a finite digit automaton with zero padding. Its proof
combines exponential representation peaks from repeatable branching loops
with an injective last-visit encoding for loop-unique automata, then transfers
the resulting polynomial word count to natural-number prefix counts.

This excludes a stationary finite-memory digit construction. It does not
exclude general sets, nonstationary digit constructions, or constructions
with unbounded memory. No global witness or universal contradiction was
obtained. The original Spec.lean remains unchanged.

Further review did not supply the missing mixed-period estimate. In
particular, slowly changing a prime still introduces variable integer
quotient terms, and a tapered initial fine-field row would require estimates
for incomplete quadratic root counts not supplied by the complete-root
character-energy theorem. Neither is being asserted as a new theorem.

## Automatic-core continuation

`AutomaticCoreExplore.lean` now proves that any automatic subset B of a
hypothetical witness A satisfies count(B,N)/count(A,N)->0 at all natural
cutoffs. Thus if A=B union D, the augmentation D must account for asymptotically
all the counting mass. The theorem is compiled and axiom-audited; see
`AutomaticCoreProgress.md`.

This closes off a sparse augmentation of a finite-automaton core. It does
not exclude nonautomatic cores or a general construction. The mixed-count
review did not find a valid inference from separate self-flatness to mixed
flatness; the previously checked reflection counterexample still applies
to that proposed finite gluing step. No main-conjecture proof was obtained.

## Nonstationary repeat-and-pad continuation

`PrefixCopyExplore.lean` and `RepetitionChainExplore.lean` now exclude
arbitrary-scale chains formed solely by repeating the entire preceding
prefix and adding empty padding. This is not restricted to a fixed base
or bounded-memory automaton. The exact Tauberian count profile gives the
adjacent-block copy budget sqrt(2)-1, so eventual full copying is impossible;
without further copying the chain stabilizes to a finite set.

Both files compile, and `PrefixCopyAxiomCheck.lean` audits the main results
using only the permitted axioms. Details are in `PrefixCopyProgress.md`.
This blocks direct iteration of cyclic padding, but does not exclude a
procedure that substantially thins or replaces the copied patterns. No
such thinning with the needed transition mixed counts has been proved.
The original conjecture and Spec.lean remain unchanged and unresolved.

## Infinite fixed-tolerance positive construction

`InfiniteLogApproximationExplore.lean` now proves a genuine infinite
fixed-relative-error analogue: for every epsilon>0, some A and c>0 satisfy
|r_A(n)/log n-c|<=epsilon c eventually. Individual exponential tails are
summed, so the threshold is uniform in the final cutoff and envelope
compactness applies. All principal results compile and pass the axiom audit;
see `InfiniteLogApproximationProgress.md`.

The coefficient is 400/epsilon^2 for small epsilon. Consequently this does
not provide a fixed-c sequence of tightening envelopes. The main conjecture
in Spec.lean remains unchanged and unresolved.

## Dilation-invariant core continuation

`DilationCoreExplore.lean` proves that a subset of a hypothetical witness
which is closed under multiplication by a fixed m>1 has zero relative
counting mass. A union repair of such a core must supply asymptotically all
the counting mass. This excludes square-closure constructions even with
arbitrary nonautomatic choices of kernels, but does not exclude general A.
The main results compile and pass the permitted-axiom audit; see
`DilationCoreProgress.md`.

Nonstationary digit constructions were reconsidered without a valid new
all-target transfer. Coordinate products still have representation peaks;
changing field encodings still lacks controlled mixed counts at intermediate
integer scales. No unrestricted solution was obtained in this continuation.
Spec.lean remains unchanged with its original sorry.

## Fixed-coefficient density-one continuation

`DensityOneLogLimitExplore.lean` now proves that for every fixed c>0 there
exist A and a harmonically summable, density-zero exceptional set E such
that r_A(n)/log n tends to c outside E. The same coefficient is retained
through all tolerances. Continuous exponential costs, finite Bernoulli
selection, and compactness give the result; all principal declarations
compile and pass the axiom audit. See `DensityOneLogLimitProgress.md`.

This does not settle the conjecture: the exceptional targets remain, no
all-target asymptotic upper envelope is supplied, and the harmonic weight
is too weak to invoke the existing actual-deficit completion theorem.
Spec.lean is unchanged and the original existential statement is unresolved.

## Uniform-envelope strengthening of the density-one construction

The same potential construction now provides a global O(log n) upper bound
at all targets, in addition to fixed-c convergence outside a harmonically
summable exceptional set. For c>128 it can also give positive logarithmic
lower bounds at every sufficiently large target. Main results are in
`UpperDensityOneLogLimitExplore.lean`, compiled and axiom-audited; see
`UpperDensityOneLogLimitProgress.md`.

This supplies the coarse global envelope for packet repair, but not its
asymptotic upper coefficient or its weighted actual-deficit summability.
No pointwise improvement resolving those two requirements was proved.
Spec.lean remains unchanged and the original conjecture unresolved.

## Polynomial exceptional-count continuation

The positive fixed-coefficient construction has been strengthened again:
for each fixed epsilon>0, the same A has a bad-target set with summable
weight (n+2)^(-1+alpha) and count o(N^(1-alpha)) for some alpha>0 depending
on epsilon. The same A retains the earlier uniform envelopes and the
harmonically summable diagonal exception set. The joint endpoint is
`PowerExceptionalCountingExplore.lean`; all principal results compile and
pass the permitted-axiom audit. See `PowerExceptionalProgress.md`.

The tolerance-dependent saving does not reach the uniform deficit-weight
criterion required for completion, and the all-target upper coefficient
is still not c+o(1). No unrestricted witness or contradiction was obtained.
Spec.lean remains unchanged and unresolved.

## Controlled-spike non-implication check

`DensityOneNoLimitExplore.lean` now constructs a globally O(log n)-bounded
representation function that converges to 1 outside a harmonically summable,
density-zero exceptional set, but has no finite pointwise limit. It uses
the checked sparse matching repair to plant logarithmic spikes at fourth
powers, with only o(log n) unintended changes. This is a counterexample to
sufficiency of the auxiliary conditions, not a disproof of Erdős 66. See
`DensityOneNoLimitProgress.md`. The original Spec.lean remains unchanged
and unresolved.

The spike counterexample has also been strengthened in
`PowerExceptionsNoLimitExplore.lean`: the same set retains a positive
power saving in exceptional counts at every fixed tolerance, as well as
the global logarithmic bound and the masked density-one limit, but still
has no finite pointwise limit. The saving may vary with the tolerance.
The new theorem is compiled and axiom-audited. This strengthens only the
auxiliary non-implication result, not a universal obstruction.

The finite-family review still does not provide mixed estimates through
a modulus change. Same-field character identities and the row-sparse
prefix estimates cannot be applied as different-modulus compatibility
lemmas. No compatible all-target infinite construction or universal
contradiction was obtained. Spec.lean remains unchanged and unresolved.

## Fixed-tolerance completion refinement

`FixedToleranceCompletionExplore.lean` now shows that existence of a
sublogarithmic allowance with summable actual deficit is EQUIVALENT to
summability of the repair weight on every fixed lower-deviation set.
Consequently separate power exponents alpha(epsilon)>1/2 suffice; they
need not share a common positive margin above 1/2.

`CountingPowerCompletionExplore.lean` gives a count-only version: each
fixed lower-deviation set may have its own O(N^theta(epsilon)) bound with
theta(epsilon)<1/2. Together with the all-target asymptotic upper bound c,
this yields a superset with the exact limit c. Both files compile and
pass permitted-axiom audits. See `FixedToleranceCompletionProgress.md`.

These are conditional reductions, not a construction of the required
base. The previously selected fixed-c set has not been proved to satisfy
either the sub-square-root exception bounds at every tolerance or the
correct all-target upper coefficient. No mixed-period gluing theorem was
obtained in the accompanying review. Spec.lean is unchanged and unresolved.

## Ordered dependent-rounding construction

A new unconditional construction in `PrefixBalancedUpperLimitExplore.lean`
produces a set with prefix discrepancy <=1 from the exact harmonic
fractional profile and eventual upper bound r_A(n)<=6 log(n+2). More
generally it preserves prefix discrepancy <=1 for any [0,1] profile with
convolution coefficient c>=0 and gives upper coefficient 2c+4.

The finite engine rounds nonnegative multilinear upper-MGF polynomials by
ordered sum-preserving two-coordinate steps, retaining every prefix
floor/ceiling bracket. A summable upper-potential tail and joint compactness
yield the infinite set. Five new production files compile and their main
theorems pass the permitted-axiom audit; see `OrderedRoundingProgress.md`.

This supplies a bounded-discrepancy rounding without superlogarithmic
peaks, but not vanishing normalized quadratic error or the exact pointwise
limit. Negative-tilt costs are not covered by the nonnegative-coefficient
rounding theorem. The original Spec.lean remains unchanged and unresolved.

## Prefix-preserving two-sided continuation

The negative-tilt gap in ordered dependent rounding has now been closed, with a
uniform exp(2|t|) compensation per target. The same infinite set can retain prefix
discrepancy <=1, fixed-c density-one convergence, summable power-saving exceptions
at each fixed tolerance, and constant-width global envelopes. See
`PrefixBalancedTwoSidedProgress.md`; eight production files compile and their
principal declarations pass the permitted-axiom audit.

This still does not eliminate exceptional targets or give the required o(log n)
quadratic error. No main-conjecture solution is asserted. Spec.lean is unchanged.

## Local-difference continuation

The harmonic rounding can now be chosen with the previous two-sided summable
power potentials AND uniform local difference count <=24 log(N+2) for every
positive shift in every sufficiently late window [N,2N). This is checked in
`LocallySparsePowerProfileExplore.lean`. The finite engine combines positive
multilinear costs with the compensated negative-tilt costs; local difference
edges split into two matchings. Joint compactness retains all constraints.
Nine new production files compile and pass the permitted-axiom audit. See
`LocallySparseProgress.md`.

This gives structural control potentially useful for count-preserving local
repairs, but no such convergent repair has been proved. The small-tolerance
exception sets still need not be sparse enough for the existing repair
criteria. Spec.lean remains unchanged and the main conjecture unresolved.

## Count-preserving predecessor-packet continuation

A new finite repair replaces each selected free endpoint with its preceding
old point. Distinct predecessor cells give prefix changes in [-1,0],
independent of the number of moves. Uniform selection now handles bounded
fibers and combines Sidon, forbidden-choice, cell-collision, and mixed-hit
constraints. A symmetric 2m-point packet gives exactly 2m new representations
at its center and at most six self-representations elsewhere.

The candidate bounds are now checked using ordinary representation counts:
new-point hits cost local occupancy; deleted-point hits cost at most H times
r_A(z), where H bounds predecessor-fiber size. This avoids the invalid use
of local difference bounds for distant-window interactions. A concrete
interval repair and its large-scale parameter criterion compile and pass
permitted-axiom audits. See `PredecessorRepairProgress.md`.

These results remain finite/one-target. They do not improve the small-tolerance
exception-count exponents, provide the exact all-target upper coefficient,
or prove a compatible infinite repair schedule. Spec.lean is unchanged and
unresolved. No submission has been made.

## Infinite distinct-cell compatibility and capacity

`InfinitePredecessorReplacementExplore.lean` now proves that arbitrarily
many simultaneous moves in distinct ORIGINAL predecessor cells preserve
all prefix counts within one. At any cutoff, the active inserted set is
finite by injection of its predecessor image into that finite prefix.
Representation counts likewise reduce to finite active replacements.

`PredecessorPacketCapacityExplore.lean` proves a matching restriction:
pairwise disjoint packets of size at least delta log N, all supported below
2N and using distinct original cells, can have only o(sqrt N) targets per
scale under a fixed logarithmic representation envelope. Thus optimizing
the probabilistic collision budget cannot remove this geometric capacity
boundary for disjoint packets. Deliberate point reuse is not excluded.

Both files compile and pass the permitted-axiom audit. See
`InfiniteCellCapacityProgress.md`. The known exceptional-set estimates still
do not meet this boundary, and no point-reusing correction or mixed-modulus
scale compatibility theorem was obtained. Spec.lean remains unchanged and
unresolved; no submission has been made.

## Shared-point template review

The exact reusable-template identity is now checked: opposite translations
of Sidon halves U,V retain the whole designated profile 2*pairs(U,V,z), with
at most four extra self representations at every target. Conditional on
uniform old/template mixed bounds, this gives a simultaneous profile repair
using |U|+|V| points rather than separate packets per center.

The same continuation checks why free translation is not a solution to the
mixed problem: it only shifts the uniform mixed peaks. Graph-label rigidity
also proves there is only one free displacement per connected bipartite
shared-endpoint component; an odd cycle removes even that freedom. A fully
reused rectangle requires the exact additive rectangle relations among its
centers. A Sidon second-moment budget quantifies, but does not rule out,
possible point reuse. See ReusableTemplateProgress.md.

All three new production files compile and pass permitted-axiom audits. No
compatible template for the actual defect profile has been constructed, and
no new all-target infinite argument or disproof was obtained. Spec.lean is
unchanged and unresolved; no submission has been made.

## Prefix-balanced triple-sparse continuation

One new infinite harmonic rounding now simultaneously retains prefix
error at most one, all two-sided power costs, and central triple counts
bounded by 36(h+4)+2 on every fixed polynomial horizon z<=N^h. Both endpoints
at the repaired sum n must be at least N, n<=4N, and n!=z; the third point
need not be in the same window. Positive matching polynomials, summable
horizon-tail budgets, and compactness give this joint construction.

Exact upper-half endpoint deletion reduces a selected central target by
2k while losing at most 72(h+4)+4 representations at any other tested
target, independent of k. The conclusion persists for subsets of the
constructed set, subject to current endpoint eligibility. The cumulative
loss over a family T of centers is still bounded only by a sum of triple
counts (at most 2|T|R under a uniform bound). No all-target o(log n)
cumulative estimate was obtained. See TripleSparseProgress.md.

All new production files compile and pass the permitted-axiom audit.
Spec.lean remains unchanged and unresolved; no submission has been made.

## Joint boundary control and unconditional local clipping

The latest continuation removes the prior central-endpoint eligibility
hypothesis for local downward clipping. One set now retains prefix error
at most one, all two-sided power costs, arbitrarily small logarithmic
boundary coefficients, and constant central-triple bounds for every fixed
comparability factor and polynomial horizon. A general positive-pattern
compactness interface and polynomially weighted test encoding ensure all
these properties belong to the SAME set.

From every subset B of that set, any positive logarithmic cap can eventually
be attained at a chosen target n by deleting central upper-half endpoints,
with at most one unit of target overshoot and a fixed off-target loss on
z<=n^g. The collateral bound is independent of the deletion size. See
JointBoundaryClippingProgress.md and JointLogarithmicClippingExplore.lean.

This is still local. Later corrections may destroy earlier lower bounds,
and no o(log n) cumulative loss estimate or deficit-filling schedule was
proved. All principal new results compile and pass the permitted-axiom
audit. Spec.lean remains unchanged and unresolved; no submission was made.

## High-coefficient host, two-sided reset, and exhaustive absorption

One structured host now has a positive all-target lower envelope, small
boundary coefficients, and constant central triple intersections. Every
subset can be reset at one late target to floor(log n), with at most one
unit of target overshoot and constant off-target collateral on polynomial
horizons. See `HostResetAbsorptionProgress.md`.

The cumulative union-of-edits footprint bound and coordinate stabilization
are checked. More importantly, the canonical restore-then-upper-delete
recipe is now proved to FAIL under an exhaustive increasing-target schedule:
at target 2a it restores every host point a, and subsequent upper-half
clipping never deletes a. Its limit therefore recovers the host outside a
finite prefix. A genuine coordinatewise-convergent schedule is constructed
whose moving-target normalized counts tend to 1 but whose limiting set's
counts do not tend to 1. This blocks the naive diagonal inference.

All principal new declarations compile and pass permitted-axiom audits.
No all-target witness or universal disproof has been obtained. Spec.lean
remains unchanged and unresolved, and no submission has been made.

## Monotone upper clipping and a prefix deletion budget

`MonotoneClippingExplore.lean` now constructs, for every host A and cap
q(n)>=1, one subset C satisfying r_C(n)<=q(n) at every target. Only larger
endpoints are deleted; all coordinates below N are final after stage 2N.
The number of removed points below N is bounded by the sum of original
half-excess counts below 2N. `ClippingBudgetTransferExplore.lean` proves
preservation of a normalized counting limit if this explicit budget is
negligible at that normalization.

No negligible budget at all shrinking tolerances has been established for
the existing coefficient-one host. No lower-envelope conclusion follows
from clipping, and even count preservation would not remove the previously
checked dyadic-hole obstruction. See `MonotoneClippingProgress.md`.
Both production files compile and their main results pass permitted-axiom
audits. Spec.lean is unchanged and unresolved; no submission has been made.

## Range-independent finite mixed families

A new asymmetric energy estimate controls mixed character fibers using only
the SHORTER interval's self-energy. Summably weighted translate selection
and levels D(j+1)^2 then give nested finite-field families with starting
spacing D and repair-band width g independent of the maximum index. The
field-size threshold is linear in the largest actual level. All targets,
including the repaired origin, have the asserted relative mixed-count bound.
The result transfers to actual cyclic sets with a thickness threshold also
independent of the maximum index. Scalar nominal levels have arbitrarily
fine multiplicative coverage after a fixed starting index.

See `RangeIndependentFamilyProgress.md`. All principal new results compile
and pass permitted-axiom audits. Actual-cardinality coverage is a proposed
next finite step, not yet a conclusion. No compatibility between different
moduli or all-target infinite construction has been proved. Spec.lean is
unchanged and unresolved; no submission has been made.

## Sparse-start complete palette continuation

Actual-cardinality coverage has now been checked for the older linear-index
families. By beginning at I=ceil(4/epsilon)+1 and tuning the base coefficient
to c/I^2, the complete palette can start at a member B0 whose ACTUAL mean
|B0|^2/M is within the prescribed tolerance of c log M. Every cardinality
from |B0| to M is covered with factor 1+epsilon, and every pair of members
retains the requested relative mixed flatness about its actual mean.

See SparseStartPaletteProgress.md. All three production files compile and
pass the permitted-axiom audit. This supersedes the prior statement that
actual-cardinality coverage is only proposed. It does not supply integer
scale transitions, and dense-member placement still has its mass cost.
Spec.lean remains unchanged and unresolved; no submission has been made.

## Uniform mixed endpoint-prefix control for complete palettes

The sparse-start complete palette now also admits uniform spatial control.
OuterMixedPrefixExplore.lean proves an exact floor/ceiling bound for the
number of endpoints in ANY prefix of an outer-repeated mixed cyclic pair.
With fixed repetition factor K and sufficiently small input error, each
prefix has error <=eta times the actual outer mixed mean; arbitrary endpoint
intervals have error <=2eta times that mean.

PrefixBalancedPaletteExplore.lean combines this with the logarithmic sparse
start, nested cardinality coverage through full density, and mixed flatness.
Tuning the input coefficient to c/K and taking M large preserves coefficient
c at N=MK. Both files compile and pass the permitted-axiom audit. See
PrefixBalancedPaletteProgress.md.

The error is relative to the FULL cyclic mean, not the mean in a tiny
interval. No estimates between different moduli, preservation of an old
integer prefix, or cutoff-independent finite-prefix feasibility are proved.
Thus the compactness hypothesis is still missing. Spec.lean is unchanged
and unresolved; no submission has been made.

## Actual integer step-profile realization

The endpoint-prefix palette estimates have now been transferred to actual
integer interval pieces, with exact clamped overlap endpoints handling all
carries. Disjoint assembly gives a uniform error bounded by
(2 eta/M)(sum_i |C_i|)^2. Cardinality-level quantization then gives

    |r_A(n)-mu F(n)|
      <= [(1+2 eta)R^2-1] mu (sum_i w_i)^2.

Consequently every FIXED finite family of bounded positive step heights has
arbitrarily large finite integer realizations with
|r_A(n)/log M-c F(n)|<=delta at EVERY natural n. The interval endpoints may
be chosen after M. See IntegerStepRealizationProgress.md. All four new
production files compile and pass the permitted-axiom audit.

The number and heights of steps are fixed before the modulus, and the
threshold depends on them. This does not give uniform feasibility down to a
fixed initial integer cutoff as M grows, or preserve an old integer prefix
through a modulus change. Thus it is not the missing compactness hypothesis.
Spec.lean remains unchanged and unresolved; no submission has been made.

## Prescribed-prefix extension within one palette

The finite integer assembly result now preserves an arbitrarily prescribed
old family of pieces from the SAME joint palette. Old membership and every
representation count below the cutoff are exactly unchanged; all new points
lie beyond the cutoff, and the first-window increment is exactly the mixed
old/new term. The all-target profile estimate remains valid without
reselecting old members.

An unconditional theorem chooses arbitrarily large finite palettes supporting
all such later prescribed old families, with normalized error <=delta about
the fixed weighted overlap profile. See PalettePrefixExtensionProgress.md.
All three new production files compile and pass the permitted-axiom audit.

The modulus and palette still precede the admissible old prefix in the
quantifier order. No transfer of an existing prefix to a new modulus or
cutoff-independent infinite compatibility principle is established. Spec.lean
is unchanged and unresolved; no submission has been made.

## Uniform finite operator for bounded monotone profiles

The number-of-pieces restriction has been removed for bounded monotone
profiles. One finite pointwise rounding rule Phi, chosen before the profile,
works for every antitone f on [0,M) with 1<=f<=W, giving

    |r_{Phi(f)}(n)/log M-c normConv(M,f,n)|<=delta

at every natural target. Agreement of input prefixes gives exact agreement
of output prefixes and their representation counts. A fixed height grid has
interval fibers because the profile is antitone; the number of grid levels
is independent of the original profile's number of changes. The geometric
profile-to-discrete-convolution identity is checked explicitly.

See MonotoneProfileOperatorProgress.md. All five new production files compile
and pass the permitted-axiom audit. W remains fixed before M, and different
moduli still have no proved compatible operators. Thus this is not yet the
cutoff-independent finite-prefix condition needed for the conjecture.
Spec.lean is unchanged and unresolved; no submission has been made.

## Joint mixed finite monotone-profile operator

The finite causal rounding operator has been strengthened to control mixed
counts for EVERY PAIR of bounded monotone profiles, simultaneously under one
fixed rule. The target is the exact normalized discrete mixed convolution.
The profiles may have different interval partitions. The proof uses joint
mixed endpoint-prefix bounds directly; it does not infer mixed control from
separate self-flatness. See JointMonotoneOperatorProgress.md.

All five new production files compile and pass the permitted-axiom audit.
This is compatibility between profiles within ONE modulus, not between
operators at different moduli. The height range remains fixed in advance.
No compatible infinite chain or universal contradiction has been proved.
Spec.lean is unchanged and unresolved; no submission has been made.

## Shared-point repair capacity

BoundedReuseRepairExplore.lean now replaces packet disjointness by an explicit
point-reuse bound L. Double counting gives sum_i |P_i| <= L count(B,N).
Under a global logarithmic representation envelope, logarithmic-sized packets
supported below 2N obey delta^2 log N * |T|^2 <= 4N(K+4C)L^2. Thus even growing
reuse L=o(sqrt(log N)) forces |T|=o(sqrt N).

For a monotone hypothetical completion with the same counting asymptotic as
its base, bounded reuse of new points gives the stronger
|T| sqrt(log N)/sqrt N -> 0. See BoundedReuseRepairProgress.md. All eight main
results compile and pass the permitted-axiom audit. These are necessary
conditions on correction procedures, not a universal obstruction. No original
conjecture proof or disproof was obtained; Spec.lean remains unchanged.

## Independently translated palette pieces

The finite prefix-balanced palette may now be closed under every cyclic
translation without changing cardinalities or the logarithmic coefficient.
Exact wraparound formulas cost at most a factor three in endpoint error.
This phase closure is not nested. A two-family integer assembly theorem then
allows independently chosen phases on each of a fixed finite list of pieces,
with a uniform exact-profile estimate. See PhaseTranslationProgress.md.

All three production files compile; the nine principal results pass the
permitted-axiom audit. These remain same-modulus finite results, not arbitrary
pointwise phase control or a compatible infinite density schedule. The
original conjecture is still unresolved and Spec.lean is unchanged.

## Whole-row reflection diagnostic

SymmetricRowPeakExplore.lean proves an exact two-carry decomposition for a
cyclically reflected row. Every natural set containing that whole row has a
representation peak at least half the row cardinality. Thus a global
logarithmic envelope bounds such a row by O(log(a+p)). Horizontal fibers of
the parabola unions are reflected, and arbitrary horizontal phases only
change their reflection center. See SymmetricRowPeakProgress.md.

The seven principal declarations compile and pass the permitted-axiom audit.
This diagnostic is not asserted for arbitrary clipped pieces or pointwise
phase changes, and is not a disproof of the conjecture. Spec.lean remains
unchanged and unresolved.

## Unrestricted shared-point repair incidence

UnrestrictedRepairIncidenceExplore.lean removes packet bookkeeping entirely:
total gain on T plus the new/new count equals twice the new-point incidences
into T. If a same-counting-profile monotone completion fills persistent
positive deficits, its new points must exhibit arbitrarily large normalized
target-degree concentrations. In the logarithmic setting the normalization
is |T_N| sqrt(log N)/sqrt(N). See UnrestrictedRepairIncidenceProgress.md.

All nine principal results compile and pass the permitted-axiom audit. No
uniform degree bound for the constructed base's exceptional targets, or for
all possible completions, has been proved. Hence this remains a necessary
condition on repair, not a universal obstruction. Spec.lean is unchanged and
unresolved.

## Antitone within-row reflection diagnostic

AntitoneRowPeakExplore.lean extends the whole-row diagnostic to a selected
row that is not itself symmetric. If every selected upper endpoint retains
its reflected partner, its upper-endpoint cardinality is bounded by an
integer representation peak. Antitone position-dependent palettes sharing
one reflection have precisely this property. The translated parabola-row
specialization is checked. See AntitoneRowPeakProgress.md.

All seven principal results compile and pass the permitted-axiom audit.
The bound concerns selected upper endpoints, not arbitrary row cardinality;
independently varying phases and arbitrary clipping are not covered. No
universal contradiction or infinite construction follows. Spec.lean remains
unchanged and unresolved.

## Constructive common-prime, different-thickness compatibility

CoprimeThicknessExplore.lean now gives an actual mixed-count transfer between
two coprime coordinate thicknesses over the same prime. Rectangular radix
subtraction and high-digit CRT retain the borrow exactly; averaging it loses
only min(K,L)(mu+E), so the total mixed error is KL E+min(K,L)(mu+E).
The natural-index identification with vertically rescaled versions of the
existing thickenings is checked for every n. Exact cardinalities and actual
mixed means are also checked.

UniformCoprimeThicknessExplore.lean selects one plane family before all
later admissible thickness pairs. See CoprimeThicknessProgress.md. All six
production files compile and all 17 audited declarations use permitted
axioms only. This is same-prime compatibility, not a field-change or infinite
prefix theorem. The original conjecture remains unresolved and Spec.lean
unchanged.

## Joint same-prime thickness continuation

The exact periodic-pattern comparison now transfers the old same-thickness
bounds to left/left and right/right pairs in the new CRT modulus. Together
with the previous left/right estimate and checked commutativity, all four
mixed pair types are controlled. The uniform joint family requires BOTH
thicknesses large. A common outer lift also supplies endpoint-prefix bounds.

See JointCoprimeThicknessProgress.md. Four production files compile; all 16
principal audited declarations use only the permitted axioms. The plane
family is chosen before all later thicknesses and outer repetitions. This
still gives no change-of-prime or cutoff-independent infinite-prefix theorem.
Spec.lean remains unchanged and unresolved.

## Pair-weighted aggregate continuation

PairWeightedCharacterEnergyExplore.lean extends the character-energy engine
from separable weights to arbitrary pair-weight matrices, charging squared
Frobenius mass. PairWeightedRootTransferExplore.lean transfers this to every
fine root-count target. UniformMatrixSpanExplore.lean chooses a translation
before all later coefficient vectors in a fixed finite span.

AdaptiveMatrixEnergyExplore.lean checks the quantifier limitation: for any
fixed admissible translate, a nonnegative zero-one matrix can have energy
at least h^3/8 and mass at most h^2. A universal later-matrix energy constant
must therefore grow at least linearly in h. This is not a universal
obstruction to Erdős 66.

See PairWeightedTransferProgress.md. Four production files compile and all
13 audited principal declarations use only the permitted axioms. These
remain weighted root-count and finite-span results; no compatible infinite
coarse profile or original-conjecture proof has been obtained. Spec.lean is
unchanged and retains its original sorry.

## Fixed-translate color selection and actual-set continuation

`FixedTranslateColorProgress.md` records a checked finite selection of coarse
colors AFTER the sign pattern / field translate is fixed. Matching moments,
retained diagonal energy, and a joint centered potential control both the
signed root error and the unsigned deterministic mean. One translate can
precede all later finite symmetric kernel data; only the coloring changes.

`ActualColorTransferProgress.md` closes the arbitrary coarse-overlap
multiplicity issue for this finite pipeline. An oriented-edge repair makes
fine palettes disjoint with mixed-count matrix L1 error <=10h+8, including
the origin. Exact product assembly then gives an actual-set error theorem
for arbitrary overlapping coarse colors. The 12 new production files
compile; two audits check 34 declarations with only the allowed axioms.

This still does not construct the needed infinite coarse profiles or
compatible changes of integer period. Permanently retaining the sparse
fine support contradicts the already proved residue equidistribution
necessary condition. No infinite witness or universal contradiction was
obtained. Spec.lean remains unchanged with its original sorry.

## Complete-partition continuation

`CompletePartitionTransferProgress.md` records four new compiled files.
Parallel parabolas give a complete disjoint fine partition and an actual-set
color transfer with no old sign-energy or origin-repair term. Two audits
check 21 principal declarations using only the permitted axioms.

The normalization now depends on the full field size; for sparse kernels
the current relative squared-error bound scales like field size / target
mean. Thus it cannot simply be substituted into the previous sparse-label
logarithmic regime. The finite-family budget still has no infinite profile.
Moreover every whole horizontal row retains reflection symmetry under all
coarse color assignments, and the corresponding integer row peak is checked.
No compatible recursive integer construction was proved. Spec.lean remains
unchanged and unresolved.
