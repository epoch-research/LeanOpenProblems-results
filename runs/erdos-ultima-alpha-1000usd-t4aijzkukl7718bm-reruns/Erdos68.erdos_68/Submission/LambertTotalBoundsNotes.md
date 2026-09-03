# Exact Lambert row sums and total raw-operator bounds

This is auxiliary verified progress, not a settlement. Spec.lean still contains
its original sorry; there is no completed proof or disproof.

LambertTailRows.lean and LambertTotalBounds.lean compile and have built oleans.
Their printed principal axiom audits use only propext, Classical.choice,
and Quot.sound.

## Exact row sum

LambertTailRows defines row(n,k)=r_(k+2)(n), where

    r_d(n)=1/((d!)^floor(n/d)*(d!-1)).

It proves summability, the exact row decrement at multiples of d, and

    sum_(k>=0) r_(k+2)(n) = alpha - prefixQ(n).

Here prefixQ is the rational Lambert prefix. It also proves that every finite
raw operator commutes with this infinite row sum, with summability verified.

## Total bound

IMPORTANT INDEXING: K in LambertTotalBounds is the NUMBER of cancelled rows.
Its operator List.range' 2 K uses d=2,...,K+1. For n>=4,
range_operator_explicit_bound proves

    |rawApply_[2,...,K+1](alpha-prefixQ)(n)|
      <= 2^(K+1)/(K+1)^(floor(n/2)-1).

The proof removes the annihilated rows, applies the previously verified
per-row bounds, and proves a telescoping p-series estimate:

    sum_(k>=0) 1/(k+K+2)^m <= 1/(K+1)^(m-1),  m>=2.

In the boundary-lattice notes, K denotes the FINAL cancelled row. Thus the
same bound there is 2^K/K^(floor(H/2)-1), for K>=2 and H>=4.

## What is still missing

The common denominator and finite pigeonhole bound are now verified; see
LambertBoundaryFrameworkNotes.md. Their asymptotic selection of parameters
is not yet Lean formalized. More importantly, those
estimates would supply only a small-or-zero form. No uniform theorem giving
a nonzero small integer form, or two independent small coefficient pairs,
has been obtained. The finite LLL computations do not provide such a theorem.
