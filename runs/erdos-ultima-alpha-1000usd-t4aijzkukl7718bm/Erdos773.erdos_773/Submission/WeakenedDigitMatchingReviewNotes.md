# Weakened digit matching review

The original conjecture is still UNSETTLED. No Lean source was changed in
this review, no new bound was proved, and no incomplete proof was submitted.
Spec.lean retains its sole admission at line 17287 for 0 < epsilon < 1/3.
Its completed endpoint remains eventual M(N) >= N^(2/3).

## Coherence is stronger than the necessary arithmetic condition

The established MatchingCoherenceBound applies to a code criterion that
reconciles coordinate-wise pair matchings WITHOUT using a scalar norm
identity. It should not be used to exclude every digit construction.

If two pairs of digit words have equal column sums, their evaluated root
sums are equal. Together with equality of the two scalar square sums,
this identifies the unordered pairs of nonnegative integer roots. Thus a
construction would not need blanket coordinate coherence if the actual
integer norm equation also forced those column sums to agree.

No such column-sum lifting theorem was found. Reducing a square-sum
identity modulo the radix only controls the lowest square-digit sums.
After they are cancelled, the next condition includes weighted cross
terms, not another isolated equality of digit-square sums. The remaining
carry constraints cannot currently be replaced by formal polynomial
coefficient identities.

## Formal irreducibility and checksum variants

FormalGaussianSidon is already a complete polynomial-ring result with a
large admissible alphabet. Its integer specialization is the unresolved
issue, and FormalGaussianSpecialization supplies an actual counterexample
to the blanket transfer rule. No new carry-safe high-cardinality subclass
or useful carry-collision count was obtained here.

The finite-field norm checksum idea has also already been tested beyond
its successful base-three instance. Its verified failures include genuine
extension-field arithmetic, not only arithmetic modulo a composite base.
Neither anisotropy of a field norm nor irreducibility of its defining
polynomial supplies the missing correspondence between integer carries
and field operations. No new uniform checksum identity was derived.

These observations do not rule out more sophisticated carry-aware codes.
They do not improve the actual Sidon exponent or supply the negation of
the original quantified conjecture.

Main-file SHA-256:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940
