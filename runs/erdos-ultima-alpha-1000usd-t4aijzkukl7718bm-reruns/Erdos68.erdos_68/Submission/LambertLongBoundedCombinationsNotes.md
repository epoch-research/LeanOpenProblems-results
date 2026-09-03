# Nonvanishing for arbitrarily long bounded integer combinations

Verified auxiliary progress, NOT a proof or disproof of Erdos 68.
`Spec.lean` remains unchanged with its original `sorry`.

`LambertLongBoundedCombinations.lean` compiles without warnings, has a built
olean, and all five principal axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Main theorem

Use d>=12 and the operator cancelling rows 2,...,d-1. Let integer weights
w_0,...,w_M be not all zero, and suppose

    |w_j| <= Q,    4Q <= d!,
    H >= (d+1)*(log2(Q)+2*log2(d)+135).

Then `raw_detection_explicit` proves that there is an index H<=n<H+d with

    sum_(j=0)^M w_j * rawTail(d-2,n+j) != 0.

There is NO upper bound on M. Unlike the previous d-consecutive-sample
result, this theorem restricts the integer coefficient height instead of
the support length. All original-series tails are retained.

## Proof

Write lambda=(d!)^(1/d). First suppose w_0!=0, and group the coefficients
by residue modulo d:

    c_h=sum_(j congruent h mod d) w_j/lambda^j.

The nonconstant terms of c_0 start at j>=d. Bounding even the terms not in
that residue class by a full geometric tail gives

    |c_0-w_0| <= 2Q/lambda^d = 2Q/d! <= 1/2.

Since w_0 is a nonzero integer, ||c||>=1/2. The previously verified cyclic
inverse and cancelling-product estimates therefore detect a first-row
combination of normalized magnitude at least

    exp(-48)/(2*(lambda+1))

in every d-phase window. Also sum |w_j|/lambda^j<=2Q independently of M.
The remaining-row bound gives a total contribution at most exp(-48)/(2d)
when 4Qd^2<=2^L and H>=(d+1)*(L+130). Since lambda+1<d, it cannot cancel
the detected first row.

For an arbitrary nonzero vector, trim to its earliest nonzero weight and
shift the detecting window back. This preserves the stated threshold.
Taking L=log2(Q)+2*log2(d)+5 gives the explicit form above.

Principal declarations:

* aggregate_zero_lower
* row_detection
* raw_detection
* raw_detection_nonzero
* raw_detection_explicit

## Remaining arithmetic gap

The detected sum still has a rational boundary. This theorem does not
assert its integrality, and a weight vector clearing one output phase need
not clear the phase detected by the theorem. The present simultaneous
clearing or small-integer-matrix counting estimates need weights larger
than the permitted factorial budget in the examined quadratic-window
scaling; see LongBoundedCombinationReviewNotes.md.

No small nonzero integer-form family, infinite actual-carry residue
violation, or complete proof/disproof of the original conjecture has been
obtained. No numerical search was run in this continuation. All compilation
and axiom checks have completed; nothing remains pending.
