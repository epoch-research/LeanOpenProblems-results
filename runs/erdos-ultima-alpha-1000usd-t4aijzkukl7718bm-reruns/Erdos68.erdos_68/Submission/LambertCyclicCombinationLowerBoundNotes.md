# Height-independent nonvanishing for short raw combinations

Verified auxiliary progress, not a settlement of Erdos 68. `Spec.lean`
remains unchanged with its original `sorry`.

`LambertCyclicCombinationLowerBound.lean` compiles without warnings and has
an olean. Its four principal axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Cyclic inverse estimate

Put lambda=(d!)^(1/d) and f(h)=lambda^h.val/(d!-1) on ZMod d. Then

    lambda*f(h)-f(h+1) = 1 if h+1=0, and 0 otherwise.

For cyclic convolution (c*f)(h)=sum_i c(i)*f(h+i), this gives

    lambda*(c*f)(h)-(c*f)(h+1)=c(-h-1).

Consequently ||c||/(lambda+1)<=||c*f|| in the sup norm. This estimate
has no coefficient-height hypothesis.

Convolution commutes with the previously verified cancelling operators.
Their normalized inverse-norm bound is at least exp(-48). Thus every
nonzero real vector of d consecutive weights has a detectable phase
in the first uncancelled row.

## Full-target conclusion

Use K=d-2 cancelled rows, so the first uncancelled row is d. For d>=12,
any nonzero real vector w indexed by ZMod d, and

    H >= (d+1)*(3*(log2(d)+1)+130),

`raw_combination_explicit_window` proves that some H<=n<H+d satisfies

    sum_i w(i)*rawTail(d-2,n+i.val) != 0.

The threshold is independent of the weights. The proof controls the
remaining rows by exp(-48)/d^2 after normalization; their weighted total
is smaller than the detected first-row term because lambda+1<d.

The result implies nonsingularity of the d-by-d Hankel block of these
raw errors. This consequence is now formalized in
`LambertRawHankelNonsingular.lean`; see its accompanying notes.

## Limitation

These are raw errors with rational boundaries, not integer linear forms.
The existing simultaneous boundary-clearing construction for all d
output phases has an index cost of approximately C^d. No proof has been
obtained that a sufficiently small cleared vector is detected, or that
the corresponding cleared determinant tends to zero. The nonvanishing
statement alone does not imply irrationality.

No complete proof or disproof of the original conjecture has been found.
