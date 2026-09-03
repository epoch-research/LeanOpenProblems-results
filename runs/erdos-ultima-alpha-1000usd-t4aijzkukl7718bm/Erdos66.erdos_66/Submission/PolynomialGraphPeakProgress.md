# Polynomial graphs over square moduli: peaks and thinning bounds

The original conjecture remains unresolved. Spec.lean is unchanged with its
original sorry. None of the following restricted-class obstructions is a
negation of Erdos66.erdos_66.

## Verified files

* PolynomialGraphPeakExplore.lean
* PolynomialGraphSubsetExplore.lean
* PolynomialGraphOverlapExplore.lean

All three compile and have current oleans. PolynomialGraphPeakAudit.lean and
PolynomialGraphOverlapAudit.lean audit eleven principal declarations using
only propext, Classical.choice, and Quot.sound. No production sorry or new
axiom was added. The files named *Checks.lean are name-search scratch files;
some have deliberate failed checks and are not production dependencies.

## Ordinary encoding and modular symmetry

For f:ZMod M -> ZMod M, encode its graph by

    g(x)=x.val+M*(f x).val.

The encoding is injective and lies below M^2. If T distinct inputs x_i have
partners y_i, with ordinary input sums x_i.val+y_i.val=X and modular output
sums f(x_i)+f(y_i)=s independent of i, then the ordinary graph sums lie in
just two targets:

    X+M*s.val, X+M*(s.val+M).

Pigeonholing gives a representation peak at least floor(T/2), at a target
below 2M^2. Actual natural antidiagonals are used; modular counts are not
silently identified with natural counts.

## Polynomial graphs over M=H^2

Every increment H*t is square-zero in ZMod(H^2). The exact Taylor identity
therefore gives, for every polynomial P and every input residue a modulo H,

    P(a+H*t)=P(a)+P'(a)*H*t  mod H^2.

At a=0, pair t with H-1-t. There are H such inputs with the required symmetry,
so the graph has a peak >=floor(H/2), below 2H^4.

For H=2^(k+1), the peak is at least 2^k. It survives a natural translation
L<=H^4 and occurs below 4H^4=64*16^k. Consequently, a set containing one such
translated graph for every k has no finite logarithmic limit. The polynomials
may vary with k, and the graphs need not be nested. Moving each graph into a
new annulus does not remove the obstruction.

## Arbitrary thinning

Inside a single input residue class a modulo H, any retained input subset S
has at most 4H distinct ordinary graph sums. The input parameter sum t+u has
fewer than 2H possibilities, and each modular output sum has at most two
ordinary lifts.

Thus a representation cap B below 2H^4 forces

    |S|^2 <= 4H B.

Cauchy--Schwarz over the H input residue classes gives

    m^2 <= 4H^3 B,

where m is the total number of graph points retained. This is proved both
for explicit row families and for the actual set of all graph inputs whose
encoded points belong to A. The input-grid equivalence is checked, so m
counts actual distinct graph points, not a multiplicity convention.

For a global envelope r_A(n)<=K+C log(n+2), K,C>=0, the verified real bound is

    m^2 <= 4H^3 [K+C log(2H^4+2)+1].

The extra one is the cost of taking a natural ceiling of the cap. For every
delta>0, eventually in H, uniformly over ALL polynomials P over ZMod(H^2),

    m < delta H^2.

The formal statement indexes H=n+1 to avoid a zero-modulus instance. This
uniform vanishing-fraction conclusion is proved first for a logarithmic
envelope, then for every finite logarithmic representation limit.

## Scope and important distinction

These are polynomial functions over a ring with nonzero nilpotents. They
are NOT arbitrary functions on ZMod(H^2), and they are NOT polynomial graphs
over a field of cardinality H^2. In a field there is no nonzero square-zero
increment, and the Taylor-linearization argument does not apply.

No theorem extracting a positive-density polynomial-graph portion from an
arbitrary hypothetical witness has been proved. General nonlinear sparse
sets can avoid these local affine restrictions. Nor has a compatible
nonanalytic digital construction been supplied. The conjecture therefore
remains neither proved nor disproved.
