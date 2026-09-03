# A prime-indexed row remainder (verified auxiliary fact)

This is NOT a settlement of Erdős 68. The conjecture in Spec.lean remains
unchanged with its original sorry, and no proof or disproof has been submitted.

`PrimeRowRemainder.lean` compiles without warnings, has a built olean, and its
four principal printed axiom audits list only propext, Classical.choice,
and Quot.sound.

## Exact formula

For every odd prime p, set N=2p-2. The file proves

    fract(N!/(p!-1)) = 1-1/p + N!/((p!)^2*(p!-1)),
    1-1/p < fract(N!/(p!-1)) < 1.

The rightmost inequality is the general fractional-part bound. In particular,
the displayed positive correction is strictly less than 1/p.

Proof ingredients:

* The known congruence choose(2p,p)=2 mod p^2 and the central-binomial
  recurrence imply p divides Catalan(p-1)+1.
* N!/(p!)^2 = Catalan(p-1)/p exactly.
* Catalan(p-1)<p!-1. For p=3 this is direct; for p>=4 use
  centralBinom(p-1)<=4^(p-1)<p*(p!-1). The latter bound is proved by induction.
* N!/p! is an integer. Removing it and the integer part of
  Catalan(p-1)/p from the two-term geometric expansion proves the formula.

## Consequence for the actual row tail

For alpha equal to the target sum, set

    T_n=n!*alpha-sum_(k=2)^n floor(n!/(k!-1)).

Every individual fractional row is strictly less than T_n: all the other
row fractions are nonnegative, and the omitted original tail is positive.
Consequently

    T_(2p-2)>1-1/p.

Euclid's theorem then gives, for every real c<1 and every N, an n>=N with
T_n>c. This is `frequently_tail_gt`.

## Limitation

Rationality would force T_n to be a positive integer eventually, which is
entirely compatible with this lower bound. No GCD defect, nonintegrality,
small nonzero integer form, or irrationality conclusion follows here.

A further review of row/column cancellation and boundary-lattice minima
has not provided the missing nonvanishing or quantitative estimates. The
original conjecture is still unresolved in this workspace.
