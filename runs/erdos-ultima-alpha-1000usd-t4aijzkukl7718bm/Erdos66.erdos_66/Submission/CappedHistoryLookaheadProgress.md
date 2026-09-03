# Global upper caps and accurate histories do not guarantee next-window extension

## Original task status

Erdos66.erdos_66 remains unproved and undisproved. Submission/Spec.lean is
unchanged, including its original sorry. No proof has been submitted.
The new result is an obstruction to a universal extension criterion, not
a negation of the original existential conjecture.

## New checked theorem

For every c>0, 0<epsilon<c, R>=1, prescribed lookahead H, and starting
bound N0, there are N>=N0, L>=R*N with H<L, and a finite C subset [0,L)
such that:

* C contains no integer at most H;
* r_C(n)/log n < c-epsilon/4 at EVERY target;
* |r_C(n)/log n-c| < epsilon for EVERY N<=n<L;
* EVERY A agreeing exactly with C below L satisfies

      r_A(L+H)/log(L+H) <= c-epsilon.

Thus no exact-prefix extension can maintain the same strict accuracy on
[L,2L). The failing target is L+H; H is prescribed BEFORE constructing
C and may be positive, so this is not just an endpoint-notation issue.
The global cap is strict, with a fixed positive coefficient buffer.

## Proof

Start with a finite upper-bounded annulus centered at c-epsilon/2 with
accuracy epsilon/4, good on [N,(R+2)N] and supported above H+1. Since it
is finite and c-epsilon>0, its normalized count eventually vanishes.
Let m be the FIRST target at or above N with ratio <=c-epsilon. Then
m>(R+2)N, and all targets from N to m-1 have the desired strict accuracy.
Set L=m-H and truncate the set below L.

The initial gap implies that all representations at m=L+H already use
only points below L: an endpoint at least L would have its partner at
most H. The same is true in every exact-prefix extension, which retains
the initial gap. Consequently no later insertion can change the failed
count at m. Ordinary monotonicity preserves the global upper cap after
truncation, and finite locality preserves all earlier counts.

## Files and verification

* CappedHistoryLookaheadExplore.lean (three declarations, no placeholders)
* CappedHistoryLookaheadAudit.lean
* CappedHistoryLookaheadAudit.log

The production file compiles without warnings and has a current olean.
The audit reports only propext, Classical.choice, and Quot.sound.

## Quantifier distinctions

This strengthens the earlier history-only obstruction by retaining a
strict GLOBAL upper cap. Unlike NearScalePrefixObstructionExplore, it
fixes the bad old prefix first and rules out every exact-prefix extension.

Unlike the earlier future-peak theorem, this theorem requires exact
membership preservation, including old absences. It does NOT assert that
arbitrary supersets adding previously absent points below L still fail.

The prefixes are specially chosen bad ones. A successful construction
could choose good prefixes with additional lower-lookahead invariants;
this theorem neither rules that out nor shows such an invariant can be
maintained. It also does not supply bounded counting discrepancy or a
fixed infinite sequence of increasingly accurate past estimates.

The cutoff-independent finite feasibility in conjecture_iff_finite_prefixes
remains unproved. The common-source mixed-period estimates still have the
wrong own-period density scaling for direct iteration. No construction
or universal contradiction settling the original conjecture was obtained.
