# Centered Mellin estimate on growing frequency ranges — verified

The conjecture is STILL UNSOLVED. Spec.lean remains unchanged with its
original sorry. No irrational counterexample has been found, and no
completed proof has been submitted in this continuation.

New file: CenteredMellinFrequencyRange.lean.
It compiles. Principal declarations audit with only propext,
Classical.choice, and Quot.sound.

## Actual improvement

Write

    a_U(n) = (mu_{>U} * zeta)(n),
    m(U) = sum_{d<=U} mu(d)/d.

The older estimate was

    ||sum_{M<n<=2M} a_U(n) n^(it)||
        <= (1+|t|)*(M*|m(U)|+2U).

The new proof retains the center BEFORE partial summation. For every
0<U<=M and every j>=0,

    |sum_{M<n<=M+j} a_U(n) + j*m(U)| <= 2U.

This yields the centered Mellin estimate

    ||sum_{M<n<=2M} [a_U(n)+m(U)] n^(it)|| <= 2U*(1+|t|),

and, after restoring the constant mean,

    ||sum_{M<n<=2M} a_U(n) n^(it)||
        <= M*|m(U)| + 2U*(1+|t|).

Thus |m(U)| is NO LONGER multiplied by 1+|t|. This is an actual stronger
estimate; no polynomial-frequency Mobius theorem or quantitative Mertens
rate is assumed.

## Growing uniform range

If U(k)->infinity, eventually U(k)<=M(k), and U(k)/M(k)->0, then for every
epsilon>0, eventually in k, SIMULTANEOUSLY for every real t with

    |t| <= M(k)/U(k)^2,

one has

    ||sum_{M(k)<n<=2M(k)} a_{U(k)}(n) n^(it)|| <= epsilon*M(k).

The normalized budget is exactly bounded by

    |m(U(k))| + 2*U(k)/M(k) + 2/U(k),

which tends to zero by the existing qualitative reciprocal Mobius limit.
No rate is silently substituted for that limit.

## Balanced growing-cutoff specialization

At U=growingCutoff(u), M=u^3, define

    T(u)=u^3/U^2.

The file proves T(u)->infinity (indeed T(u)>=u^2 eventually) and uniform
o(M) cancellation for ALL |t|<=T(u), with the actual Vaughan divisor
coefficient. This extends the old compact-frequency-only statement on
these balanced blocks.

The limitation is also verified:

    T(u)/u^3 -> 0,
    T(u)/u^6 -> 0.

Consequently this range still does not resolve the floor strip at outer
scale N=u^6, which requires frequencies of order N. The previous
supremum/energy power-loss calculation remains relevant to the uncontrolled
high-frequency part. No full four-factor lower bound follows from this
new estimate alone.

## Other checks in this continuation

A renewed bounded external reference lookup failed at DNS resolution.
No external settlement or applicable new imported prime-pair theorem was
verified. No claim to such a theorem was used.
