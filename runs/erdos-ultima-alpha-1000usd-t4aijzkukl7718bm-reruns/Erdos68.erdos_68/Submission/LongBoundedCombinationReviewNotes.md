# Longer bounded combinations: an analytic extension and a counting gap

This is informal mathematical review, NOT a newly Lean-verified theorem
and NOT a settlement of Erdos 68. `Spec.lean` is unchanged with its original
`sorry`. No complete proof or disproof was obtained in this continuation.

## Possible extension beyond d consecutive weights

Let d>=12, lambda=(d!)^(1/d), and let w_j be a nonzero finitely supported
integer vector, with |w_j|<=Q and 2Q<=d!-1. Let m be its earliest nonzero
index. Group its rescaled coefficients by residue modulo d:

    c_h=sum_(j congruent h mod d) w_j/lambda^j.

In the residue class of m, multiplication by lambda^m gives

    w_m + sum_(r>=1) w_(m+rd)/(d!)^r.

The latter tail has absolute value at most Q/(d!-1)<=1/2. Since w_m is
a nonzero integer, ||c||>=1/(2*lambda^m). Also

    sum_j |w_j|/lambda^j <= 2Q/lambda^m,

using lambda>=2. Thus the cyclic inverse bound from
`LambertCyclicCombinationLowerBound.lean` can be extended mathematically
to arbitrary support length under this coefficient-height restriction.
The remaining-row estimate then gives phase detection once
H is of order d*(log Q+log d). This argument is recorded here for review;
the arbitrary-support extension has NOT been formalized in Lean.

## Why the present counting estimate still does not apply

Put d=K+2 and use the raw operator cancelling rows 2,...,K+1, with
M=K(K+3)/2 and P=product_(k=2)^(K+1) k!. Suppose there are D input
samples and d consecutive output phases beginning at H. The common
factorial clearing endpoint is

    T=H+(D-1)+(d-1)+M,
    C=T!/P.

Under a hypothetical rational value q of alpha, clearing by q.den*C
makes the raw-error matrix integral. Its entries are small compared with
C, so one can try integer-kernel pigeonholing using the error matrix,
rather than simultaneous modular clearing. This improvement must retain
the factor C and the full endpoint T.

For fixed positive a,b and the scaling H~a*K^2, D~b*K^2, Stirling's formula
gives the leading terms

    log C = (2a+2b+1/2)*K^2*log K + O(K^2),
    log(error upper bound) = -a*K^2*log K + O(K^2).

Counting exact images of a D-dimensional integer box in d output
coordinates therefore requires, with these uniform estimates, a coefficient
budget whose logarithm has leading size

    (2+a/b+1/(2b))*K*log K.

In contrast the preceding sufficient digit-separation restriction gives
log Q <= log((d!-1)/2) = K*log K+O(K).
These sufficient bounds do not overlap. The improvement from counting
small integer errors rather than arbitrary residues does not repair this
particular construction.

This is NOT an impossibility theorem for all windows, all lattice methods,
or every way of detecting a nonzero form. It does not supply an asymptotic
lower bound for actual useful lattice minima. No new finite numerical search
was run, and no complete original-conjecture argument resulted.

## Other reviewed routes

The existing rectangular truncation and joint Padé investigations already
retain the full-target remainders and reduced denominator costs. They do
not provide a compatible infinite family. The original factorial-scaled
tail is not completely monotone, as already proved by
`OriginalTailDifferences.negative_difference`; the separate-column sign
argument cannot simply be transferred to it.

Nothing remains running or pending compilation from this review.

## Subsequent Lean verification

`LambertLongBoundedCombinations.lean` now formalizes an arbitrary-support
version with the slightly stronger coefficient hypothesis 4Q<=d! and the
explicit threshold H>=(d+1)*(log2(Q)+2*log2(d)+135). Its principal audits
use only the permitted axioms. See LambertLongBoundedCombinationsNotes.md.
The arithmetic counting gap described above remains unresolved.
