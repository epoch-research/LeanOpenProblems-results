# Reduced numerators of exact rational residuals cannot descend

Verified auxiliary work, NOT a proof or disproof of Erdős 68.
Submission/Spec.lean remains unchanged with its original sorry. No settlement
has been obtained or submitted.

RationalTailReducedHeight.lean compiles without warnings and has a built olean.
All four printed principal axiom audits contain only propext, Classical.choice,
and Quot.sound. The file contains no proof holes or numerical proof premises.

## Definitions and denominator bound

Let

    alpha = sum_(k>=2) 1/(k!-1),
    S_N = sum_(2<=k<N) 1/(k!-1),
    r_N(q) = q-S_N, q rational.

The prefix definition includes indices zero and one with zero summands; the
file verifies its equality to the correctly shifted original real prefix.
All denominators and numerators below are those of fully reduced rationals.

For EVERY rational q and m>=9, the theorem
nearby_residual_denominator_large proves that at least one of

    den(r_(8m^2)(q)), den(r_(8m^2+m)(q))

is at least m^(m^3). The endpoint q cancels in the difference of these two
residuals. The earlier reduced block denominator bound is m^(2m^3), and the
denominator of the difference divides the product of the endpoint denominators.
Thus no multiplier involving den(q) is lost in this argument.

## Numerator bound

Suppose q>=alpha, including the hypothetical equality q=alpha. For every
N>=2, the first omitted term gives

    r_N(q) > 1/N!,
    num(r_N(q))*N! > den(r_N(q)).

For m>=9 and N<=8m^2+m,

    N! <= N^N <= m^(27m^2).

For m>=28, m^3>=28m^2. Combining these estimates with the denominator bound
proves nearby_residual_numerator_large: at least one of

    num(r_(8m^2)(q)), num(r_(8m^2+m)(q))

is strictly greater than m^(m^2).

The corollaries residual_numerators_unbounded, no_eventual_numerator_bound,
and no_eventual_numerator_descent show that these reduced numerators exceed
any fixed bound arbitrarily late. In particular they are not eventually
nonincreasing, even after all cancellation in each residual has been performed.

## Scope and status

The earlier RationalTailNotes.md explained growth only for product-cleared
numerators and left open whether reduction could supply a descent. This new
result addresses the actual reduced numerators. It does not exclude a different
integer height or a different approximation construction.

Crucially, numerator growth is compatible with rationality of alpha. This is
an obstruction to a proposed proof method, not a contradiction and not an
irrationality criterion with its premise proved. No infinite carry violation,
small nonzero integer-form family, or other settlement was obtained.

No numerical search was run. The compilation log is
/tmp/rational_tail_reduced_height.log. All checks have completed; nothing is
pending. The original Spec.lean SHA256 remains
607758b4290b62b0bf71c669432cc353dc853751c80c03b336f8fc51ca4f552d.
