# Spatially balanced complete logarithmic palettes

## Original task status

Erdos66.erdos_66 in Submission/Spec.lean remains unproved and undisproved.
Spec.lean is unchanged. No proof has been submitted.

## Exact mixed-prefix engine

`OuterMixedPrefixExplore.lean`, namespace Erdos66OuterMixedPrefix, defines

    prefixCount(M,B,C,z,u) = #{a in B : a.val<u and z-a in C}.

For the outer repetition of B,C from modulus M to modulus M*K, set
R=cyclicCount(M,B,C,reduce(z)). For every 0<=u<=M*K,

    floor(u/M) R <= prefixCount(M*K,lift(B),lift(C),z,u)
                   <= (floor(u/M)+1) R.

This is an exact natural-number bound. The proof decomposes residues into
a small residue and a block index. Each residue contributes either floor(u/M)
or at most floor(u/M)+1 block indices.

Cardinalities and actual means obey

    |lift(B)| = K|B|,
    actualMean(M*K,lift(B),lift(C)) = K actualMean(M,B,C).

If |R-mu|<=sigma mu, then the prefix error about its spatially proportional
mean is at most

    ((K+1)sigma+1)mu.

In particular, if sigma<=eta/4 and eta K>=2, every prefix error is at most
eta times the actual outer mixed mean. This holds uniformly in the target
and cutoff, for every pair satisfying the original mixed-flatness bound.

`intervalCount` counts endpoints in [u,v). The exact identity

    intervalCount(u,v)+prefixCount(u)=prefixCount(v)

then gives error at most 2 eta times the actual mixed mean for every such
interval. This is an ABSOLUTE error relative to the full mixed mean, not a
relative error with respect to the possibly tiny interval's own mean.

## Complete finite palettes with all these properties

`PrefixBalancedPaletteExplore.lean` proves

    Erdos66PrefixBalancedPalette.exists_prefix_balanced_complete_palette.

For c,tau,eta,epsilon>0, eta,epsilon<=1, and every lower modulus bound N0,
it returns an odd N>N0, a nonempty B0 subset ZMod N, and a nested finite
palette P with:

* B0 in P and B0 contained in every member;
* |actualMean(N,B0,B0)/log N-c|<tau;
* all mixed cyclic counts accurate to eta times their actual means;
* all mixed endpoint-prefix counts accurate to eta times their actual means;
* the full group in P, and |P|<=N+1;
* for every |B0|<=x<=N, a member B with x<=|B|<=(1+epsilon)x.

Choose the fixed odd repetition factor

    K=2 ceil(2/eta)+1.

Apply the sparse-start complete palette at coefficient c/K, tuning tolerance
tau/(2K), and mixed tolerance eta/4. Choose its modulus M sufficiently large
that c log K/log M<tau/2. Outer repetition preserves nesting, full membership,
and cardinality coverage. The exact mean scaling and log(MK)=log M+log K
retain the requested logarithmic coefficient at the new modulus N=MK.

## Verification

Both production files compile and have built oleans. Principal declarations
are checked in PrefixBalancedPaletteAudit.lean. Only propext,
Classical.choice, and Quot.sound occur. Neither new production file contains
sorries or new axioms.

## Scope and remaining gap

This controls arbitrary endpoint cutoffs, rather than just the two integer
carry fibers. It permits finite same-modulus spatial estimates to be made
without assuming an unproved equidistribution of roots.

It does NOT give mixed counts between different moduli or a natural-number
extension preserving an old accurate prefix. The prefix error is measured
against the FULL cyclic mean. In particular, its quantifiers do not give
uniform accuracy on all fixed integer targets as the modulus grows. The
thresholds required by Erdos66Compactness.conjecture_iff_finite_prefixes
must be chosen before the final cutoff; no such family is supplied here.

The earlier repeated-copy obstruction still applies to attempting to iterate
outer repetition literally. Dense palette members still have their integer
placement cost. No new infinite compatibility principle or universal
contradiction has been proved.
