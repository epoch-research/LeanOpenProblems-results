# Reduced-denominator recurrence investigation (not a solution)

This is mathematical reasoning, not a new Lean-verified theorem. It neither
proves nor disproves the conjecture in `Spec.lean`.

Let S_N=a/b be the reduced partial sum, with b>0, and let d=(N+1)!-1.
Put

    h=gcd(b,d), B=b/h, D=d/h, u=a*D+B, g=gcd(u,h).

Then

    S_(N+1) = u/(h*B*D),
    den(S_(N+1)) = h*B*D/g = lcm(b,d)/g.

Indeed, gcd(B,D)=1 and gcd(a,b)=1 imply gcd(u,B)=gcd(u,D)=1.
Thus the only cancellation in u/(h*B*D) is gcd(u,h). In particular g divides
h. If b and d are coprime, there is no cancellation and the new denominator
is b*d. If they are not coprime, the value of the numerator modulo h is
essential; prime support alone does not determine the reduced denominator.

This is consistent with the verified cancellation at prime 139 in
`CorrectedDenominatorCancellation.lean`. There is no justification for
assuming that the last included denominator divides the reduced denominator
of a partial sum or a corrected approximation.

## Why this does not close the irrationality argument

A large reduced denominator of a partial sum does not itself prove that its
limit is irrational. The relevant small-integer method would need a family
of rational approximations R_N=A_N/B_N for which

    0 < |B_N*alpha-A_N| -> 0.

For ordinary partial sums, the known positive tail is of factorial scale,
whereas termwise clearing is of much larger product scale. The recurrence
above does not give the small *upper* bound on B_N needed to overcome this.
It also does not prove infinitely many changes of the separately defined
factorial-grid approximants `upperApprox`.

No such denominator estimate or infinite-change result was obtained in this
investigation. The conjecture remains unproved; no proof was submitted.

## Library/literature check

A further local Mathlib search found no irrationality theorem applicable to
this exact reciprocal-factorial-minus-one series. A request for the problem's
reference page failed because the host could not be resolved; no external
paper or claimed resolution was obtained or used.
