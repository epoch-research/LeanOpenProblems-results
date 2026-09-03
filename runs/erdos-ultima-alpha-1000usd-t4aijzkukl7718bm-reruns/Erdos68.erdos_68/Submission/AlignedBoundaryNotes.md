# Exact zero-aligned boundary and eventual error growth

This is verified auxiliary work, NOT a settlement of Erdős 68. The original
`Submission/Spec.lean` is unchanged with its original sorry. No complete
proof or disproof has been obtained or submitted in this continuation.

Both new files compile without warnings, have built oleans, and contain no
proof holes. Their principal axiom audits contain only propext,
Classical.choice, and Quot.sound.

## AlignedBoundaryIdentity.lean

Let S_j^L be the rational Lambert prefix, alpha the original target, N>=2,
and let z_0,...,z_N be arbitrary integer weights. Put A=sum z_j. Assume
that these weights annihilate every geometric row d=2,...,N at indices
0,...,N. Then `boundary_of_row_cancellation` proves exactly

    sum_(j=0)^N z_j*S_j^L = A*sum_(d=2)^N 1/(d!-1).

The proof first expresses each finite prefix as a finite sum of geometric
row deficits, since rows d>N have not yet contributed at j<=N. Interchanging
two finite sums and applying the row-cancellation hypotheses proves the
identity. No heuristic asymptotics or numerical evidence is involved.

For the explicit weights from AlignedRowAnnihilator.lean, this yields:

* aligned_boundary: the displayed identity;
* aligned_error: for every real x, the weighted form is exactly
  A*(x-sum_(d=2)^N 1/(d!-1));
* aligned_boundary_integral: the boundary is integral when every d!-1
  divides A;
* aligned_error_pos: its value at alpha is positive when A>0.

Thus the previously informal zero-aligned boundary identity is now fully
Lean-verified. These forms are exactly the ordinary original-series
partial-sum approximations, rather than new rational approximants.

## AlignedBoundaryGrowth.lean

The theorem `common_multiple_ge_factorial` proves that for N>=10000,
any positive common multiple L of all d!-1, 2<=d<=N, satisfies

    (N+1)! <= L.

It uses the existing quadratic-block bound m^(m^3)<=L. Choose
m=floor(sqrt(N)/2)-1; the proof verifies

    m>=32,
    4m^2+m<=N,
    N+1<=4(m+2)^2,
    12(m+2)^2<=m^3.

Consequently (N+1)! <= (N+1)^(N+1) <= m^(3(N+1)) <= m^(m^3).
This does not assume pairwise coprimality of the denominators.

The first omitted original term then gives

    1 < L*(alpha-sum_(d=2)^N 1/(d!-1)).

The theorem `integer_partial_error_abs_gt_one` handles any nonzero signed
integer A divisible by these denominators, by applying the natural bound
to |A|.

Finally `zero_aligned_error_abs_gt_one` applies the earlier general
row-denominator divisibility theorem to ARBITRARY integer weights supported
on 0,...,N. If N>=10000, all rows 2,...,N are annihilated, and sum z_j!=0,
then the absolute value of the full weighted form at alpha is greater than
one. Thus this entire zero-aligned construction cannot supply eventually
small nonzero forms. If sum z_j=0, the exact boundary identity instead
makes the form identically zero.

## Scope

This result concerns the zero-aligned window 0,...,N with complete
cancellation of rows 2,...,N. It is not an impossibility theorem for later
translated windows, partial or approximate cancellation, grouped-row
operators, or arbitrary boundary lattices. No useful late-boundary estimate,
infinite carry violation, or other complete irrationality argument was
obtained. No computation or compilation remains pending.
