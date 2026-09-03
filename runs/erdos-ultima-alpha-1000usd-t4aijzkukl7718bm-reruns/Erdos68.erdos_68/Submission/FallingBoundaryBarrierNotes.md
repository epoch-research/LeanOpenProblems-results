# Separate-boundary clearing obstruction for the falling-residue family

This does not settle Erdős 68. The original Spec.lean remains unchanged.

`FallingBoundaryBarrier.lean` compiles without warnings, and its olean is
built. All four principal axiom audits contain only propext,
Classical.choice, and Quot.sound.

Use the previous notation, for j>=1:

    A_j = 6^j - 2*2^j + 1,
    B_j = 3^j - 1,
    E_j = sum_(n>=2) 1/(n!)^j.

The previously verified positive forms give B_j/A_j < E_j. Define

    R_J = sum_(j=1)^J B_j/A_j.

## Verified arithmetic

For every positive integer M,

    A_J divides M*B_J  ==>  M > 2^J.

This clears the rational boundary B_J/A_J itself; it does not require
clearing all polynomial coefficients. In particular, even the REDUCED
individual denominator of B_J/A_J exceeds 2^J.

The elementary identity behind the proof is, with x=2^J and y=3^J,

    A_J=x*y-2*x+1, B_J=y-1,
    x*B_J-A_J=x-1.

Thus A_J divides M*(x-1). This is positive, and A_J>x*(x-1), so M>x.

## Verified analytic obstruction

The omitted columns alone, using their first factorial row, give

    alpha-R_J > 2^(-J).

Consequently, if M>0 clears even the last individual boundary,

    M*(alpha-R_J) > 1.

This is the theorem `separately_cleared_error_gt_one`, a statement for
all J>=1, rather than a finite numerical check.

## Scope limitation

Clearing only the reduced denominator of the AGGREGATE R_J need not clear
B_J/A_J separately. The divisibility premise above has not been established
for such a reduced aggregate denominator. Cancellation among the separate
boundaries must not be excluded without proof. Nor does this obstruction
apply automatically to other polynomial kernels or to removing rational
initial rows before truncating columns.

No complete proof or disproof of the conjecture has been obtained.

## Aggregate cancellation addressed for this fixed family

The later `FallingAggregateBarrier.lean` supplies a different, stronger
obstruction to convergence to zero for the fixed two-node family. The
first column alone leaves the error

    E_1 - 2/3 > 1/20.

All later normalized column errors and the omitted columns are positive.
Consequently alpha-R_J>1/20 for every J>=1. Multiplication by ANY positive
integer retains this uniform lower bound, including the reduced aggregate
denominator. `not_tendsto_scaled_errors` formally excludes convergence to
zero for every truncation subsequence and every positive integer multiplier.

This does not extend the earlier divisibility premise to the aggregate.
It bypasses divisibility entirely using a persistent analytic gap. The
new file compiles without warnings, has an olean, and all four principal
axiom audits use only the permitted axioms.

The result treats the fixed two-node residue construction only. Increasing
the interpolation degree could shrink the first-column gap, and is not
excluded by this theorem. No solution of Erdős 68 has been obtained.
