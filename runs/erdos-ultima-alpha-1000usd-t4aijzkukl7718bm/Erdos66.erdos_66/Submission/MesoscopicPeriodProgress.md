# Clipped periodic templates in shrinking windows

## Original conjecture

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged,
with its original sorry. No proof or disproof has been submitted.

## Investigation

The proposed next step was to replace templates only in clipped windows,
rather than retaining complete periodic cylinders forever. The existing
RepeatedPeriodBarrierExplore.lean ALREADY covers clipping to windows of
length comparable with their location. The new file checks the genuinely
smaller-window variant. This is not a new mixed-count construction.

## New production file and audit

MesoscopicPeriodBarrierExplore.lean compiles and has a current olean.
MesoscopicPeriodAudit.lean checks six declarations; its log lists only
propext, Classical.choice, and Quot.sound. There are no production proof
holes or new axioms. One harmless unnecessary-sequence-focus warning remains.

## Exact clipped-window restriction

Suppose r_A(n)/log n tends to a finite real c. For every sufficiently large
N, every W<=N, every d>0, and every residue r<d, assume

    {n in [N,N+W): n mod d=r} is contained in A.

Then the checked theorem gives

    W <= [(c+1)log(6N)+2] d.

Only ONE completely retained residue is needed; no assumption about the
rest of A or behavior outside the clipped window is made. If the period
is already at least W/2 the bound is immediate. Otherwise an arithmetic
progression contained in the clipped residue class supplies the bound via
its ordered representation peak.

## Two periods and the common-product resolution cost

Let N_j -> infinity and let W_j<=N_j. Suppose two such clipped retained
residues, of periods d_j,e_j>0, occur in the same window. If

    log(6N_j)^2/W_j -> 0,

then

    W_j/(d_j e_j) -> 0.

More explicitly, for EVERY fixed natural R, eventually

    R W_j < d_j e_j.

The proof uses the exact scalar inequality

    W/(de) <= X^2/W

when W<=Xd and W<=Xe, and bounds X=(c+1)log(6N)+2 by
(c+3)log(6N) at large N. Zero-width windows are handled separately rather
than silently dividing by a positive W.

Coprimality is not needed for the product bound. If d_j,e_j are coprime,
then their CRT common period is exactly the product, and eventually not
even one complete common period fits inside the window.

## Explicit mesoscopic example

For N_j=j^2 and W_j=j, the file proves

    log(6j^2)^2/j -> 0,

and derives the product-period ratio limit for clipped residues in
[j^2,j^2+j). Thus shrinking relative width alone does not make full-CRT-
period averaging feasible.

## Scope and remaining gap

This does NOT bound actual incomplete-period mixed-count error. It does
not exclude structure-aware cancellation over a short part of a product
period, noncoprime periods with large gcd, nonperiodic templates, or sparse
selection of repetition indices. It is not a disproof of the original
existential conjecture.

The previous histogram certificate and equal-fiber transfer costs remain
insufficient. The finite arbitrary-old-set field extension from
FreshPrescribedExtensionProgress.md still lacks an integer carry and
transition-mean argument. No compatible infinite construction, sharp
completion input, sublogarithmic quadratic rounding theorem, or universal
contradiction was obtained in this investigation.
