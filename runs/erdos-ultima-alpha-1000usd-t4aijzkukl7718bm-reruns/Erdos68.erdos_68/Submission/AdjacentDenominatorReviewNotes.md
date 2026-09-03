# Further review of the adjacent-denominator recurrence

This is mathematical review only, not a new Lean theorem or a settlement.
Spec.lean remains unchanged with its original sorry. Nothing was submitted.

For d_n=n!-1,

    d_(n+1)=(n+1)d_n+n,
    (n+1)/d_(n+1)-1/d_n=-n/(d_n*d_(n+1)).

The resulting direct-generating-function identity is already recorded in
DerivativeOperatorNotes.md:

    F'(z)-F(z)=2z-sum_(n>=2) n*z^n/(d_n*d_(n+1)).

Although the residual has squared-factorial decay, evaluating this identity
introduces F'(1). Rationality of F(1) does not imply rationality of F'(1).
This review did not find a way to remove that extra boundary value while
retaining a controlled integer form in F(1) alone.

## Simultaneous differential elimination considered

The factorial-power components E_j(z)=sum_(n>=0) z^n/(n!)^j satisfy
(theta^j-z)E_j=0. A common annihilating differential operator for finitely
many such components could be considered. Merely multiplying the displayed
operators does not automatically annihilate them all: the operators do not
commute. No explicit useful common operator, integer-boundary construction,
or uniform height/error estimate was obtained in this pass.

Integration by parts would require control of the other endpoint derivatives,
not just suppression of the differential residual. Removing a finite initial
row prefix also incurs rational boundary denominators. Neither issue was
resolved. This is not a completed informal proof awaiting formalization.

## Other checks

The existing shifted-pole, original-tail finite-difference, and joint Padé
notes were checked to avoid repeating their constructions or discarding their
boundary denominators. A renewed local-file/library search found no applicable
proof of the exact conjecture. No external paper was retrieved. No new finite
numerical search was run, and no computation is pending.
