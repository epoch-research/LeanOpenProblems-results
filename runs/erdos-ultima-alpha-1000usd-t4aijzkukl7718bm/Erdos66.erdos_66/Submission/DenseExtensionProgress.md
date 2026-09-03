# Conditional dense extension and error dilution

## Original task status

Erdős 66 is still not settled. `Submission/Spec.lean` is unchanged and retains
its original `sorry`. No proof or disproof has been submitted.

## Checked files

- `VariableBernoulliBoundsExplore.lean`
- `GroupRepBernoulliExplore.lean`
- `DenseGroupExtensionExplore.lean`
- `DenseCyclicExtensionExplore.lean`
- `DilutingDenseExtensionExplore.lean`

All compile and have built oleans. Principal results are audited in
`DenseGroupExtensionAxiomCheck.lean`, `DenseCyclicExtensionAxiomCheck.lean`,
and `DilutingDenseExtensionAxiomCheck.lean`. Only propext, Classical.choice,
and Quot.sound occur.

## Bernoulli infrastructure

The simultaneous concentration lemma now permits different scales V_k for
different tests, with m_k<=V_k and a common lower bound v<=V_k. Its criterion
is

    2 number_tests exp(-epsilon^2 v/8) < 1.

The chosen outcome is required to have POSITIVE product weight. This is
important: coordinates with probability one really are present in the
selected set, rather than being silently lost in a zero-weight outcome.

`GroupRepBernoulliExplore.lean` proves self-count, mixed-count, and cardinality
MGF estimates in a finite additive abelian group. An arbitrary linear order
only enumerates unordered pairs. For groups with injective doubling, the
self-mean diagonal correction lies in [0,1].

## Explicit extension means

For old C, independently include every point outside C with probability
theta in [0,1], while forcing every point of C. Let

    M=|G|, a=|C|, b=theta M+(1-theta)a,
    mu=b^2/M, nu_i=|A_i| b/M.

The expected self-count is exactly

    theta^2 M + 2 theta(1-theta)a
      + (1-theta)^2 r_C(z) + diagonal_correction(z).

The expected mixed count with any fixed A_i is exactly

    theta |A_i| + (1-theta) r_(A_i,C)(z).

Thus old mixed flatness is retained at the level of expected counts, and
the old error is diluted as density grows.

## First quantitative extension

`exists_dense_extension_actual` assumes the old C/C and A_i/C counts are
eta-flat about their actual cardinality means, with 0<eta<=1/4. If

    1 <= eta mu,
    v <= mu, v <= nu_i for every i, v <= b,
    2 ((H+1)M+1) exp(-eta^2 v/8) < 1,

then a superset B of C exists with

- self-count relative error <28 eta about |B|^2/M;
- all A_i/B mixed errors <8 eta about |A_i||B|/M;
- ||B|-b|<eta b.

`exists_dense_cyclic_extension` specializes this to odd cyclic groups and
writes the concentration condition as

    8 log(2((H+1)M+1)) < eta^2 v.

## Stronger result: no tolerance inflation

The latest theorem is

    Erdos66DilutingDenseExtension.exists_flatness_preserving_extension.

Assume 0<eta<=1, 0<g<=1, delta>0, and

    32 delta <= eta g,
    a <= (1-g)b,
    32 <= eta g mu.

Suppose C/C and every A_i/C count are eta-flat. Retain the same three lower
mean conditions v<=mu,nu_i,b and the concentration criterion with DELTA,
not eta:

    2 ((H+1)M+1) exp(-delta^2 v/8) < 1.

Then B containing C can be chosen so that BOTH its self-counts and all
A_i/B mixed counts are eta-flat about their ACTUAL cardinality means, with
strict error bounds. Also ||B|-b|<delta b.

The gap a<=(1-g)b retires at least a g proportion of the previous normalized
error. It absorbs the sampling and cardinality-normalization errors. Thus
there is no factor 28 accumulating at each step.

`extension_card_strict` additionally shows |C|<|B| when delta<=g and the
strict cardinality estimate holds. This gives a termination measure for a
prospective finite densification chain.

## What is and is not obtained

These are CONDITIONAL finite extension theorems. A complete nested palette
with a specified sequence of density levels has not yet been constructed
from them. In particular, empty old levels should not be included among
the positive-mean concentration tests; their mixed counts are trivially zero.

The no-inflation estimate suggests iterating multiplicative density steps
until near-full density, then adjoining the full group exactly. A proof
would need to maintain all pairwise estimates, control the number of tests,
and check a uniform mean threshold throughout the chain. Strict cardinality
progress bounds the number of steps by M. This is a proposed NEXT finite
step, not a theorem claimed here.

Even such a palette would NOT yet be an integer scale-transition theorem.
It does not prescribe where density levels are placed, prove the required
inhomogeneous convolution profile at intermediate scales, or cover all
sufficiently large natural-number targets. In particular the Bernoulli
criterion must not be assumed automatically at a small fixed multiple of
log M when the desired tolerance tends to zero.

## Other review in this pass

The earlier energy and residue arguments were reviewed for multiscale
amplification. No independent family of energy contributions yielding a
logarithmic-order fluctuation obstruction was obtained. The already checked
sqrt(log n) fluctuation lower bounds remain compatible with the conjecture.

## Subsequent completion

The finite chain proposed above is now checked, including its uniform test
budget, and its hypotheses have been met using logarithmically tuned sparse
families. See `CompletePaletteProgress.md`. This still does not settle the
integer placement or the original conjecture.
