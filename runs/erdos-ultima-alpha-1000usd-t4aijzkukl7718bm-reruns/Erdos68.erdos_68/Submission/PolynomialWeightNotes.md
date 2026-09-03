# Positive polynomial-weighted forms (not a solution)

Let alpha=sum_(n>=2) 1/(n!-1), and E_j=sum_(n>=2) 1/(n!)^j for j>=1.
For N>=2 define integer polynomials

    P_N(X)=product_(k=2)^N (1-k! X),
    Q_N(X)=(P_N(1)-P_N(X))/(1-X).

The displayed quotient is a polynomial over Z because its numerator vanishes
at X=1. Put

    I_N=sum_(n>=2) P_N(1/n!)/(n!-1).

Terms with n<=N vanish. For n>N every factor 1-k!/n! lies strictly between
zero and one. The existing tail bound therefore gives

    0 < I_N < sum_(n>N) 1/(n!-1)
              <= 3/(2*((N+1)!-1)).

In particular these are provably nonzero forms tending to zero. Polynomial
division, applied termwise with t=1/n!, gives the exact identity

    t*P_N(t)/(1-t)=P_N(1)*t/(1-t)-t*Q_N(t).

All involved series converge absolutely; polynomial expansion is finite.
Thus, writing Q_N(X)=sum_j q_(N,j) X^j,

    I_N = (-1)^(N-1) * product_(k=2)^N(k!-1) * alpha
          - sum_(j=0)^(N-2) q_(N,j) E_(j+1).

The first three examples are

    I_2 = -alpha + 2 E_1,
    I_3 = 5 alpha - 4 E_1 - 12 E_2,
    I_4 = -115 alpha + 116 E_1 + 84 E_2 + 288 E_3.

## What is still missing

Although all coefficients in these forms are integers, the E_j are real
constants, not integers or rationals. Rationality of alpha therefore does
NOT make I_N an integer after multiplication by its putative denominator.
The verified irrationality of each individual E_j does not repair this.

No elimination of the E_j with adequate coefficient and error estimates has
been obtained. With a polynomial P(t) alone, eliminating every moment term
in the displayed division formula would require Q=0, hence P constant;
a nonzero constant cannot also annihilate the first N summands. This does
not rule out more elaborate constructions depending on both n and 1/n!.

These are mathematical notes, not new Lean-verified declarations. They give
no proof or disproof of Erdos 68, and Spec.lean remains unchanged.
