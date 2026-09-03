# Rational series with asymptotically exact factorial growth and a two-index congruence lag

This is verified auxiliary work, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
Nothing has been submitted as a settlement.

`AsymptoticFactorialRational.lean` compiles without warnings and has a built
olean. Its three printed principal axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.

## New comparison

The theorem `exists_rational_asymptotic_factorial_series` constructs positive
natural numbers d_n such that

    (n+6)! divides d_n+1,
    d_n/(n+8)! tends to 1,
    sum_(n>=0) 1/d_n = 1/8! = 1/40320.

The explicit verified ratio bounds are

    1-4/(n+8) <= d_n/(n+8)! <= 1+2/(n+8).

This strengthens the earlier factorial-rough comparison's coarse growth
bounds: the ratio to the displayed factorial now actually tends to one.
The congruence is still two factorial indices behind that asymptotic base.
It is NOT the full congruence (n+8)! | d_n+1, and no exact shifted-divisibility
chain between successive d_n+1 is asserted.

The first denominator is exactly 46079, whereas 8!-1=40319. This is a
different series and cannot be used as `erdos_68.disproof`.

## Exact recursive construction

Write m=n+8. Starting with r_0=1/8!, define

    A=(m-2)!,  b=1/(m+1)!,
    k=floor((1/(r_n-b)+1)/A)+1,
    d_n=k*A-1,
    r_(n+1)=r_n-1/d_n.

The earlier general rounding lemmas are reused. They give

    1/(r_n-b)<d_n<=1/(r_n-b)+A,
    b<r_(n+1)<=b+A*r_n^2.

Induction proves

    1/m! <= r_n <= (1+4/m)/m!.

The step estimate reduces to

    (m+1)^2*(m+4)^2 <= 4*m^3*(m-1),  m>=8,

and is checked algebraically in Lean. The remainder is positive and tends
to zero. Telescoping then proves the exact rational sum.

The denominator bounds are obtained from the same rounding inequalities:

    (m-4)*m! < m*d_n <= (m+2)*m!.

Casting and dividing by positive factors yields the displayed ratio bounds
and the limit. No external numerical output or native decision procedure is
used as a premise.

## Scope

This rules out using only asymptotically factorial growth together with a
factorial congruence lagging by two indices. It says nothing about the exact
sequence n!-1. A new argument using its stronger exact structure is still
required. No complete proof or disproof of the conjecture was obtained.
