# Two adjacent rows make the actual rowwise tail exceed one

Verified auxiliary progress, NOT a proof or disproof of Erdos 68.
Spec.lean is unchanged and retains its original sorry. No completed proof
or disproof was found or submitted in this continuation.

`Submission/PrimeAdjacentRows.lean` compiles without warnings and has a
built olean. Its five printed principal axiom audits use only propext,
Classical.choice, and Quot.sound. It contains no proof holes.

## New unconditional estimate

Write

    alpha = sum_(k>=2) 1/(k!-1),
    F_N = sum_(k=2)^N floor(N!/(k!-1)),
    T_N = N!*alpha-F_N.

For EVERY prime p with p=1 modulo 12, the file proves

    T_(2p-2) > 1.

Dirichlet's theorem consequently gives arbitrarily large such prime
indices. This strengthens the earlier frequently-above-every-c<1 result:
the strict inequality is now above ONE itself, not just arbitrarily near
one from below.

It remains compatible with rationality, which would make T_N a positive
integer eventually (and hence at least two on this subsequence).

## Catalan arithmetic

Let C=Cat_(p-1). The existing prime-row result gives p | C+1 and

    (2p-2)!/(p!)^2 = C/p.

The new file proves p+1 | C for p=1 modulo 12. First, C is even: p*C is
the positive central binomial coefficient at p-1, which is even, and p
is odd. The exact central-binomial/Catalan identities also give

    p+1 | 2*(2p-1)*C.

Write p=12k+1, C=2d, and m=6k+1. Canceling two gives

    m | 2*(24k+1)*d.

Subtract this expression from 8*m*d to obtain m | 6d. Subtract k*(6d)
from m*d to get m | d. Thus p+1=2m divides C=2d. This avoids an
unproved assumption about the prime factors of p+1.

Put a=C/(p+1). The file verifies

    p | a+1,
    a < (p+1)!-1,
    (2p-2)!/((p+1)!)^2 = a/[p*(p+1)].

## The two row contributions

Let N=2p-2. The existing result gives

    fract(N!/(p!-1)) > 1-1/p.

For the next row, put D=p*(p+1), r=a mod D. Since p divides a+1 and D,
we have p | r+1, so r>=p-1. The geometric decomposition has an integral
first term and is

    N!/((p+1)!-1) = integer + r/D + eps,
    0 < eps = a/[D*((p+1)!-1)] < 1/D.

Because r+1<=D, there is no wrap through one. Therefore

    fract(N!/((p+1)!-1)) > (p-1)/[p*(p+1)].

All other row fractions are nonnegative. The omitted original tail,
scaled by N!, is strictly greater than 1/(N+1). Adding these three lower
bounds gives

    T_(2p-2) > 1 - 2/[p*(p+1)] + 1/(2p-1) > 1.

The last comparison is p*(p+1)>2*(2p-1), valid for p>=3. The complete
infinite tail is retained; no numerical approximation is used.

## GCD application and remaining gap

The earlier RowGcdEquality theorem says that rationality of alpha would
force

    gcd(F_N,N!) = T_N

for all sufficiently large N. Hence the new file verifies
`irrational_of_frequent_coprime_rows`: it would suffice to have arbitrarily
large primes p=1 modulo 12 with

    gcd(F_(2p-2),(2p-2)!)=1.

NO infinite occurrence of this coprimality condition has been proved.
The lower bound T>1 alone is not a GCD defect or a contradiction with
integral tails. No assertion is made that Dirichlet's theorem supplies
the coprimality condition; it supplies only the prime progression.

Principal declarations:

* catalan_even_at_odd_prime
* successor_dvd_catalan
* successor_quotient_properties
* factorial_ratio_successor
* successor_row_lower
* scaled_omitted_tail_lower
* two_rows_tail_lower
* tail_gt_one
* frequently_tail_gt_one
* irrational_of_frequent_coprime_rows

## Status

The row-GCD exact stabilization and its successive-difference criterion
were reviewed; no infinite failure of stabilization was proved. No new
numerical search was run. The finite API-check file was removed. All
compilation and axiom checks are complete, with nothing running or pending.
The original conjecture remains unproved and undisproved in this workspace.
