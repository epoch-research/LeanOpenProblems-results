# Nonuniform bounded-width digit cores

## Original task status

The conjecture in Submission/Spec.lean remains neither proved nor disproved.
The original statement, import, and sorry are unchanged. No proof submission
has been made. The file's SHA256 is still

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## New verified theorem

Fix a base b>=2 and a finite state type sigma. Allow the digit transition
relation to depend on BOTH the total word length and the digit position.
The transitions can be nondeterministic. Initial and accepting states may
also depend arbitrarily on total word length. No compatibility between
programs at different lengths is assumed. Words are zero-padded, with
least-significant digit first.

Suppose these programs recognize a subset B of A, and A obeys

    r_A(n) <= K + C log(n+2),  K,C>=0.

Then, at every natural cutoff N,

    count(B,N)^2/N -> 0.

If A is a hypothetical witness of the original conjecture, this gives

    count(B,N)/count(A,N) -> 0.

In particular, the whole witness cannot have a nonuniform bounded-width
nondeterministic digit description. This is strictly a restricted-class
obstruction, not the negation of the original existential conjecture.
The old automatic-core result required a stationary deterministic automaton;
the new theorem makes neither assumption.

## Finite digit-box engine

DigitBoxEnergyExplore.lean defines ordinary natural encoding of a length-k
base-b vector and its Cartesian digit box. The encoding is injective below
b^k. Coordinatewise equal digit sums give equal ordinary encoded sums;
carries are retained rather than replaced by digitwise group addition.

Every nonempty digit set D has a two-point subset {a,d} with

    |D| <= |{a,d}|^b.

A two-point Cartesian subbox is centrally symmetric. Swapping a_i and d_i
in every coordinate pairs all its elements at the SAME ordinary integer
sum encode(a)+encode(d). Therefore, if a Cartesian box lies inside A and
r_A(n)<=M for n<2*b^k, then its cardinality is at most M^b.

LayeredDigitProgramExplore.lean fixes boundary states for every digit.
Each fixed boundary-state path gives a contained Cartesian box. There are
at most S^(k+1) such paths, S=|sigma|. Hence

    |accepted(P)| <= S^(k+1) M^b.

This holds for nondeterministic position-dependent transitions. Overlap
between boxes causes no problem.

## Logarithmic asymptotic step

LayeredDigitAsymptoticExplore.lean proves that the global logarithmic
envelope supplies a natural L such that

    r_A(n) <= L(k+1)  whenever n<2*b^k.

Thus a recognized prefix has cardinality at most

    S^(k+1) [L(k+1)]^b.

When S^2<b, polynomial-versus-geometric decay and comparison between
adjacent base powers give count(B,N)^2/N->0 at ALL cutoffs. This intermediate
file explicitly retains S^2<b; it does not silently assume digit blocking.

## Checked blocking removes the width/base condition

LayeredPathExplore.lean defines an offset-dependent word path relation and
proves its append law and equivalence with finite boundary-state paths.

DigitBlockingExplore.lean groups d consecutive old digits into one digit
of base b^d. A grouped transition means existence of a full old-state path
through the corresponding length-d word. It retains the same state type.
The file proves:

* expansion has length d*k;
* expansion preserves the ordinary natural-number code exactly;
* expanding a padded canonical word gives the original-base padded word;
* paths through expanded words equal paths in the grouped program;
* the accepted natural-number sets agree, with their actual cutoffs.

NonuniformDigitCoreExplore.lean chooses a fixed d large enough that
S^2<b^d. It groups the program for total old length d*k, separately for
every k. The recognized set is unchanged. Applying the intermediate
asymptotic theorem in base b^d removes the numerical restriction.

## Principal declarations

Namespace Erdos66NonuniformDigitCore:

* Recognizes
* grouped_recognition
* nonuniform_subset_sq_negligible
* nonuniform_subset_negligible
* no_nonzero_log_limit

The last theorem assumes a nonuniform bounded-width description of the
entire set. It is NOT a theorem of type negating Erdos66.erdos_66.

## Files and verification

Six production files compile, with current oleans:

* DigitBoxEnergyExplore.lean
* LayeredDigitProgramExplore.lean
* LayeredDigitAsymptoticExplore.lean
* LayeredPathExplore.lean
* DigitBlockingExplore.lean
* NonuniformDigitCoreExplore.lean

DigitProgramAudit.lean audits 32 principal declarations. The saved log uses
only propext, Classical.choice, and Quot.sound. No production placeholders
or added axioms occur. DigitBlockChecks.lean, BoxChecks.lean and BoxCheck2.lean
are API-search scratch files and can contain intentionally failed checks.

## Remaining gap

No recognizability, bounded-width, or other finite-complexity hypothesis
occurs in the original conjecture. No such description has been derived
for an arbitrary hypothetical witness. The result rules out one broad
construction class but supplies neither a general infinite construction nor
a universal fluctuation contradiction. A successful construction may use
unbounded state complexity throughout essentially all its counting mass.

The most direct sufficient routes remain unresolved: uniform quadratic
Boolean rounding, cutoff-independent finite feasibility, a compatible
changing-palette construction, or a repair scheme meeting the sharp
completion hypotheses. These digit-program results do not fill those gaps.
