# Finite-state waiting-time approximations (not a solution)

This is mathematical analysis and an external exact-arithmetic experiment.
It is NOT a new Lean-verified theorem and does not settle Erdős 68.
`Submission/Spec.lean` is unchanged and no proof has been submitted.

## Rational recurrence and its limit

For s>=2 put p_s=1/s! and define rational numbers

    F_s(0)=0,
    F_s(r+1)=p_s*(1+F_s(r))+(1-p_s)*F_(s+1)(r).

One interpretation is the expected number of failures in r trials, starting
at state s: failure has probability p_s and leaves the state unchanged;
success advances the state by one. The recurrence itself does not need a
probability formalization.

Write

    A_s=sum_(n>=s) 1/(n!-1).

Since A_s-A_(s+1)=p_s/(1-p_s), it satisfies the same affine recurrence:

    A_s=p_s*(1+A_s)+(1-p_s)*A_(s+1).

Consequently E_s(r)=A_s-F_s(r) satisfies

    E_s(r+1)=p_s*E_s(r)+(1-p_s)*E_(s+1)(r).

All these errors are strictly positive. The elementary factorial-tail bound
A_s <= (3/2)/(s!-1) <= 3/s! = 3*p_s gives, by induction,

    0 < E_s(r) <= (2/3)^r * A_s.

Indeed the induction step bounds E_s(r+1) by
(2/3)^r*(A_s-p_s), which is at most (2/3)^(r+1)*A_s.
Thus the rational approximants

    R_(s,r)=sum_(n=2)^(s-1) 1/(n!-1) + F_s(r)

increase to alpha (monotonicity also follows from the finite-state
interpretation or by induction on the recurrence). Positivity and convergence
alone say nothing about the error after multiplying by a reduced denominator.

## Exact extrapolation identity

The recurrence immediately gives

    [F_s(r+1)-p_s*F_s(r)]/(1-p_s)
      = 1/(s!-1)+F_(s+1)(r).

So filtering the first geometric mode simply adds the exact row at s and
shifts the starting state to s+1. Repeating the operation removes successive
modes in the same way. It does not provide an independent source of rational
approximations beyond the family R_(s,r) already displayed.

No spectral-expansion assumption is needed for this identity.

## Exact finite checks after reduction

The 96 cases

    s in {2,3,5,10},  1<=r<=24

were computed using Python `fractions.Fraction`. For each reduced R=a/b,
the interval for b*alpha-a was obtained from

    L=sum_(n=2)^100 1/(n!-1),
    L<alpha<L+2/(101!-1).

Exactly 94 of these intervals lie above 1. The two exceptions, (s,r)=(3,1)
and (5,1), lie inside (0,1). No case was ambiguous. Selected results:

    start | trials | denominator bits | log10 scaled error (diagnostic)
        2 |      1 |                2 |       0.178113
        2 |      8 |               61 |      15.977778
        2 |     24 |              837 |     244.805685
        3 |      1 |                3 |      -0.283169
        3 |     24 |              920 |     258.421922
        5 |      1 |               10 |      -0.030904
        5 |     24 |             1109 |     302.949072
       10 |     24 |             1651 |     458.409668

The interval classifications use exact arithmetic. The logarithms are only
floating-point diagnostics. Artifacts:

* `/tmp/factorial_waiting_time_test.py`
* `/tmp/factorial_waiting_time_test.json`

These finite checks prove no asymptotic impossibility theorem. In particular,
they do not rule out a different construction, and they supply no proof or
disproof of the target conjecture.
