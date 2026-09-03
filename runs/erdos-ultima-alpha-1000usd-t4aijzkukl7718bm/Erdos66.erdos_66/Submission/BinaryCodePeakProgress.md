# Binary linear and affine code peaks

The original Erdős 66 conjecture remains unresolved. Spec.lean is unchanged
with its original sorry. The following are restricted-class obstructions,
not a disproof of the existential statement.

## Verified files

* BinaryZeroSpanExplore.lean
* BinarySupportedSubspaceExplore.lean
* BinaryLinearCodePeakExplore.lean
* BinaryCodeEnvelopeExplore.lean

All four compile and have current oleans. BinaryCodePeakAudit.lean and
BinaryCodeEnvelopeAudit.lean audit ten principal declarations, using only
propext, Classical.choice, and Quot.sound. No production sorry or new axiom
has been introduced.

## Rank lemma

For a finite vector set S in a finite-dimensional binary vector space,
there is a functional f for which the span of S intersect ker(f) has
dimension at most floor(|S|/3). No spanning hypothesis on S is needed.

The proof chooses two functionals minimizing their common-zero span W.
Every one of their four cells spans W: otherwise a separating functional
h and the perturbation (f+a h,g+b h) strictly decrease the common-zero
span. Thus the zero spans of f,g,f+g lie in the spans of the three disjoint
nonzero cells. One such cell has cardinality at most |S|/3.

Applying this in the dual space to coordinate functionals yields, in every
length-n, dimension-d binary linear code C, a codeword c and subspace W
of dimension at least d-floor(n/3), containing c, such that every x in W
is supported wherever c has bit one.

## Natural, not XOR, representation counts

Under ordinary binary encoding, for every x in W,

    encode(x)+encode(c+x)=encode(c).

For an arbitrary bit translation b,

    encode(b+x)+encode(b+c+x)=encode(b)+encode(b+c).

The affine formula allows fixed digit sums equal to two; their ordinary
carries are identical in all pairs. Injecting W into the actual natural
antidiagonal proves a peak at least 2^(d-floor(n/3)). The target is below
2^n in the linear case, and below 2^(n+1) in the affine case.

Consequently, a set containing such (affine) codes of length 6k and
dimension at least 3k for every k has no finite logarithmic limit.

## Quantitative envelope restriction

If r_A(t)<=K+C log(t+2), C>=0, and A contains an affine binary code of
length n and dimension d, then

    2^(d-floor(n/3)) <= K+C(n+2).

This follows from the finite peak and log(t+2)<=n+2 at its target.
In particular, eventually in n, no affine code of length n and dimension
at least n/2 can be contained in A. This is proved first for a global
envelope, then for every finite logarithmic limit (including zero).

## Scope

No high-rate affine-code extraction theorem for arbitrary hypothetical
witnesses has been proved. General sparse nonlinear sets need not contain
such codes. In particular, these results do not negate erdos_66.
Polynomial maps on truncated power-series rings can become affine on
high-valuation balls, but no theorem applying the present bounds to those
graphs has yet been formalized. A genuinely nonlinear digital construction
is not excluded by this work.
