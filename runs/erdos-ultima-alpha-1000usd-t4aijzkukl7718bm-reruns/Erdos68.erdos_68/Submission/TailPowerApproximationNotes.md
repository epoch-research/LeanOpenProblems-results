# Two-scale tail expansion (not a settlement)

This note contains auxiliary results, not a settlement. The conjecture in
Spec.lean remains unchanged and unproved.

## Verification update

`Submission/TailPowerExpansion.lean` now compiles and its olean has been built.
It verifies, in namespace `TailPowerExpansion`:

* `irrational_scaledColumnTail`: each scaled factorial-power tail coefficient
  is irrational;
* `scaledColumnTail_succ`: the exact coefficient recurrence;
* `finite_tail_expansion`: the identity after any finite number of columns;
* `tailError_bounds`: strict positivity beyond the first omitted row, and
  the stated geometric upper bound.

The formal parameter N corresponds to the mathematical cutoff N+1 below,
and its power parameter r corresponds to j=r+1. The three printed principal
axiom checks list only `propext`, `Classical.choice`, and `Quot.sound`.
The later product-multiplier discussion remains mathematical analysis, not
an additional assertion in that Lean file. None of these results settles
the original conjecture.

## Tail expansion

For N>=2 let F=N!, R_N=sum_(n>N) 1/(n!-1), and

    B_(N,m)=(N+1)(N+2)...(N+m),
    C_j(N)=sum_(m>=1) 1/B_(N,m)^j,       j>=1.

Positive summation of geometric series gives

    R_N=sum_(j>=1) C_j(N)/F^j.

The coefficients satisfy the exact recurrence and elementary bounds

    C_j(N)=(1+C_j(N+1))/(N+1)^j,
    1/(N+1)^j < C_j(N) <= (N+2)/(N+1)^(j+1).

The upper bound follows by bounding successive ratios in the m-sum by
1/(N+2)^j <= 1/(N+2). These are coefficients of a convergent expansion,
not coefficients of a purely formal asymptotic series.

## Exact truncation error

After retaining j=1,...,J, the remainder is exactly

    D_(N,J)=sum_(n>N) 1/[(n!)^J (n!-1)].

Writing G=(N+1)!, positivity and the same ratio comparison give

    1/[G^J(G-1)] < D_(N,J)
                    <= (N+2)/(N+1) * 1/[G^J(G-1)].

In particular, omitting every column after the first leaves an error of
order 1/((N+1)!)^2, even if the first column were evaluated exactly.

## Arithmetic limitation

The C_j(N) are NOT rational coefficients. If

    E_j=sum_(n>=2) 1/(n!)^j,

then

    C_j(N)=(N!)^j * (E_j-sum_(n=2)^N 1/(n!)^j).

Thus their individual irrationality follows from that of E_j. The exact
recurrence above is not a rational closed form for C_j(N). Treating a finite
sum of these coefficients as a rational approximation would be invalid.

Replacing every C_j(N) by a finite partial sum produces mixed geometric
truncations of the original rows, already considered in other development
files. Rational-function or Pade approximations to C_j(N) would require a
new bound for the common denominator and the combined signed error. No such
bound establishing nonzero small integer forms has been found.

There is also a limited, simple obstruction for first-column lower
approximations: if a rational approximation to C_1(N) lies below C_1(N),
then the omitted higher columns still contribute more than
1/[(N+1)!((N+1)!-1)]. Using the product multiplier

    product_(n=2)^N (n!-1)

makes that particular lower bound grow without bound, rather than tend to
zero. This observation applies to that product multiplier (or its positive
integer multiples), not to arbitrary reduced denominators. It does not
exclude cancellation from an upper approximation, or a construction using
multiple columns.

No complete proof or disproof of Erdos 68 has been obtained from this route.
No proof has been submitted.
