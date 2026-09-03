# Gcd of a Lambert coefficient window and a one-coordinate lifting cost

Verified auxiliary work, NOT a proof or disproof of Erdős 68. Spec.lean is
unchanged and retains its original sorry. No complete argument awaiting
formalization has been obtained, and no new submission check was made.

LambertCoefficientWindowGcd.lean compiles without warnings and has a current
olean. Its four printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound.

## Exact coefficient-window gcd

Write a_n for the original Lambert coefficients. For a prime p and N=p+r,
let

    G_(p,N)=gcd_(p<=k<=N) [a_k * N!/k!].

The theorem windowGcd_eq proves

    G_(p,N)=gcd(a_N,N).

This is a gcd of the INDIVIDUAL scaled coefficients. It is not the gcd of
their sum and is not the RowGcdCriterion quantity involving rowwise floors.

The proof starts with a_p=1 and uses the exact recurrence

    G_(p,N+1)=gcd(a_(N+1),(N+1)*G_(p,N)).

The known congruence a_(N+1)=1 modulo N implies that a_(N+1) is coprime to
G_(p,N), since the inductive gcd divides N. It therefore removes the old
gcd from the right-hand argument. In particular G_(p,N) is positive and
divides N.

## Bounded representation except at the first coordinate

For any integer t divisible by G_(p,N), the theorem
bounded_representation_except_first constructs integer weights w_k with

    t=sum_(k=p)^N w_k*a_k*N!/k!,
    0<=w_k<k*(k-1) for p<k<=N.

There is NO bound on w_p in this theorem.

At each backwards step, solve the congruence for the next digit modulo
N*G_(p,N-1). Bezout followed by taking an integer remainder puts that digit
in [0,N*G_(p,N-1)). The preceding gcd divides N-1, giving the quadratic
bound. The remaining carry is a multiple of G_(p,N-1), so the induction
continues. At the prime endpoint a_p=1 absorbs the final carry, without a
height bound.

## The missing endpoint bound is substantive

For any odd prime p>=3, put g=G_(p,p+1). The file proves 0<g<p+1. The upper
bound uses the least-prime-factor congruence to show a_(p+1) is odd.

Suppose integers w_0,w_1 satisfy

    g=(p+1)*w_0+a_(p+1)*w_1,    w_1>=0.

The theorem first_weight_cost proves

    p! < 2^((p+1)/2)*(1-w_0).

Indeed w_1 cannot be zero because 0<g<p+1; thus w_1>=1. The even-index
Lambert lower bound then forces the displayed cost at the first coordinate.
So even in this two-index window, retaining the nonnegative bounded-digit
choice can leave a factorial-scale first weight. The result does not rule
out longer windows. The signed extension below also rules out repairing this
two-index cost by changing the signs of its two digits.

The extension `first_weight_cost_signed` removes the condition w_1>=0 and proves

    p! < 2^((p+1)/2)*(1+|w_0|).

If w_1>=0, this follows from the preceding bound. If w_1<0, positivity of g
forces a_(p+1)<(p+1)*w_0, yielding an even stronger bound. Thus arbitrary
signed digits retain a factorial-scale first-coordinate cost in this window.
The extension compiles and its axiom audit uses only the allowed axioms.

Principal declarations:

* windowGcd_eq
* bounded_digit
* bounded_representation_except_first
* successor_windowGcd_lt
* first_weight_cost
* first_weight_cost_signed

## Remaining gap

Neither the gcd identity nor the bounded later digits supplies a bound on
the full lifted vector suitable for a small integer form. No transfer to a
controlled useful lift for the raw Lambert boundary lattice has been proved.
The separate fixed-operator nonvanishing theorem still does not apply
uniformly to the growing boundary operators.

All computations and compilations in this continuation have finished.
The original conjecture remains unproved and undisproved in this workspace.

## Longer-window extension

The separate verified LambertLongWindowCost.lean now bounds every signed
representation of the positive gcd in an even-ended window N=p+r>=4:

    (9/5)^p <= 2^(N/2+1)*W*(r+1)*(N+1),

where W bounds all absolute weights. When 2r<=p, it also proves

    (6561/5000)^p <= [2*W*(r+1)*(N+1)]^4.

See LambertLongWindowCostNotes.md. This is a lower bound, not the missing
controlled useful lift or an irrationality conclusion.
