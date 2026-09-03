# Common-source comparison across two finite periods

## Original task status

The conjecture remains unproved and undisproved. Submission/Spec.lean is
unchanged with its original sorry. No proof or disproof has been submitted.

## Verified production files

* CyclicLiftMixedExplore.lean
* ClippedTwoPeriodExplore.lean
* DyadicTwoPeriodSystemExplore.lean

All compile and have current oleans. ClippedTwoPeriodAudit.lean audits
16 lemmas/theorems; the saved log uses only propext, Classical.choice, and
Quot.sound. There are no production sorries or new axioms.

## Exact one-sided lifting identity

For arbitrary A subset ZMod M and D subset ZMod(MK),

    r_(outerLift(A),D)(z)
      = sum_(i<K) prefixCount_(MK)(outerLift(A),D,z-Mi,M).

For a source C subset ZMod L, the first-block endpoint set of
outerLift(rebase(M,L,C)) is exactly that of rebase(MK,L,C).
Hence, for arbitrary source C,D,

    r_(old(C),new(D))(z)
      = sum_(i<K) prefixCount_(MK)(rebase C,rebase D,z-Mi,M),

where

    old(C)=outerLift(M,K,rebase(M,L,C)),
    new(C)=rebase(MK,L,C).

This is an actual cyclic identity in the common period MK, not a product-
group analogy. When C is the same source on both sides, the two patterns
agree at every natural a<M, exactly.

## All four pair types

Assume MK<=L and the source mixed endpoint-prefix errors for C,D and D,C
are at most eta*mu, where mu=|C||D|/L and eta>=0. Then for every old/new
choice on each side, and every common-period target,

    |r_(type(C),type(D))(z) - (MK/L)*mu| <= 4 K eta mu.

The old/old type uses exact outer lifting, the two cross types use the new
identity and commutativity, and the new/new type uses clipping. No inference
from separate self-flatness to cross-flatness is used.

If additionally L<=2MK and 16K eta<=1, actual-mean normalization gives

    |r_(type(C),type(D))(z)-actualMean(type(C),type(D))|
      <= 32K eta actualMean(type(C),type(D)).

This handles zero-mean source pairs as well.

## Unconditional dyadic specialization

For any c,delta>0 and lower exponent bound N0, there are k>N0,
M=2^k, B subset ZMod M and C subset ZMod(2M), such that:

* B and C have the same first M membership bits;
* in the COMMON period 2M, all four pair counts of outerLift(B) and C,
  divided by log(2M), are within delta of c;
* in its OWN period M,

      |r_(B,B)(z)/log(2M)-c/2| <= delta/2.

The last factor one half is explicit in the theorem. This is not an
extension with the same logarithmic coefficient at both scales. The theorem
also does not assert that C has least period 2M: a repeated pattern is not
excluded by these hypotheses alone.

## Meaning and remaining gap

This supplies a genuine mixed-count comparison across different finite
period descriptions WHEN they are clipped from the same source. It is
stronger than a comparison of two already-identical infinite periodic
membership patterns. It does not create a source after an arbitrary short
pattern has already been prescribed.

The common-source maps preserve short bits, but unchanged source density
makes the own-period mean grow linearly with the period ratio, not
logarithmically. Retuning different source members can change density, but
then the exact same-member prefix agreement cannot be silently reused.
A piecewise construction must retain the old part explicitly and account
for its inhomogeneous overlap profile.

Finally, a witness's actual modular prefixes cannot themselves become
uniformly cyclic-flat: CyclicPrefixExplore.lean already proves a fixed
logarithmic variation in such prefixes. The new finite patterns therefore
cannot simply be identified with every full prefix of one hypothetical
witness.

No compatible infinite density schedule, source replacement theorem, or
cutoff-independent finite-prefix feasibility has been proved. Nothing here
settles the existential conjecture in Spec.lean.
