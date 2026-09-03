# Signed coefficient-gcd lifting costs in longer windows

Verified auxiliary arithmetic, NOT a proof or disproof of Erdős 68.
Spec.lean is unchanged and still has its original sorry. No complete
informal solution awaiting formalization has been obtained.

LambertLongWindowCost.lean compiles without warnings, has a current olean,
and contains no proof holes. Its three principal axiom audits use only
propext, Classical.choice, and Quot.sound.

## Setting and exact estimate

Let p be prime, N=p+r be even and at least four, and let

    g = gcd_(p<=k<=N) [a_k*N!/k!] = gcd(a_N,N).

Suppose integer weights w_i, 0<=i<=r, satisfy

    g = sum_i w_i*a_(p+i)*N!/(p+i)!,
    |w_i| <= W,    W>=0.

The theorem gcd_lift_weight_cost proves

    (9/5)^p <= 2^(N/2+1)*W*(r+1)*(N+1).

The theorem short_window_exponential_cost proves, when 2r<=p,

    (6561/5000)^p <= [2*W*(r+1)*(N+1)]^4.

The latter base is greater than one. As an immediate asymptotic consequence,
polynomial-size full weights cannot represent these gcds in such windows
for arbitrarily large p. The explicit power inequality is Lean-verified;
this note's asymptotic phrasing is not a separate limit declaration.

## Proof mechanism

The least-prime-factor congruence shows a_N is odd at an even index N.
Thus g is odd. For k<N the factor N!/k! is even, so the last weight w_r
must be odd.

Split the normalized Lambert coefficient as

    a_n/n! = u_n + e_n,
    u_n = 2^(-n/2) if n is even, and 0 otherwise,
    e_n = sum_(d|n,d>=3) 1/(d!)^(n/d).

The elementary factorial bound (9/5)^d<=d! for d>=3 gives

    0 <= e_n <= (n+1)*(5/9)^n.

Multiplying the weighted row-two sum by 2^(N/2) gives an integer. Its last
summand is w_r and every earlier nonzero summand is even. Hence that integer
is odd and has absolute value at least one. This step permits arbitrary
signs and does not discard the cancellations from the other rows.

The triangle inequality and the e_n bound give

    1 <= 2^(N/2)*[g/N! + W*(r+1)*(N+1)*(5/9)^p].

Since g is an odd divisor of even N, 2g<=N. The existing factorial lower
bound N*2^(N/2)<=N!, valid here, therefore bounds the first term by 1/2.
Rearranging gives the first displayed estimate. Taking fourth powers and
using 4*floor(N/2)<=3p gives the second.

## Scope

This is a lower bound on the full weight norm for representing the positive
coefficient-window gcd. It does not concern the rowwise-floor gcd used by
RowGcdCriterion, and it does not assert an obstruction for every Lambert
boundary pair or for the row-cancelled operators. It supplies no small
nonzero integer forms in the target constant.

The separate two-index theorem first_weight_cost_signed, in
LambertCoefficientWindowGcd.lean, gives the stronger factorial-scale bound
on its first weight without any sign restriction. Together these results
show that merely replacing nonnegative digits by signed digits does not
repair those proposed gcd-lifting constructions.

The original conjecture remains unresolved. All computations and compilations
in this continuation have finished. No new submission check has been made.
