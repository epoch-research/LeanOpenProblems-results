# Clipping cyclic moduli and logarithmic dyadic palettes

## Original task status

The conjecture is still unproved and undisproved. Spec.lean is unchanged with
its original sorry. No proof submission has been made.

## Verified files

* ClippedModulusExplore.lean
* ClippedModulusTuningExplore.lean
* DyadicCyclicPaletteExplore.lean

All compile and have current oleans. ClippedDyadicPaletteAudit.lean audits
14 new declarations. Its saved log contains only propext, Classical.choice,
and Quot.sound. There are no production placeholders or new axioms.

## Exact change of finite modulus

For 0<M<=L and C subset ZMod L, rebase(M,L,C) retains exactly the original
membership bits at integers in [0,M), read as residues modulo M. For u<=M,
its natural slice [0,u) is exactly the corresponding slice of C.

For C,D and z in ZMod M, the new endpoint-prefix count is exactly

    pairs(slice_L(C,0,u), slice_L(D,0,M), z.val)
  + pairs(slice_L(C,0,u), slice_L(D,0,M), z.val+M).

Both carry terms are included. Their geometric overlap lengths sum to u.
Consequently, if the original mixed endpoint-prefix errors are at most
eta*mu, where mu=|C||D|/L, then

    |prefixCount_M(rebase C,rebase D,z,u) - (u/L)*mu| <= 4 eta mu.

Taking u=M gives the cyclic total about (M/L)*mu. No condition that M divide
L is used. The operator preserves inclusions and takes the full group to
the full group.

If M<=L<=2M and eta<=1/16, normalization to the new actual mean nu gives

    |prefixCount_M(z,u) - (u/M)*nu| <= 32 eta nu.

The half-size hypothesis controls normalization loss, not an omitted carry.

## Tuning after the target modulus is chosen

Suppose a joint old palette has multiplicative cardinality coverage with
factor 1+epsilon, where epsilon<=1. Given a desired positive new mean w,
choose old cardinality near

    x=sqrt(w L^2/M).

If x is above the old sparse start and below L, the clipped member has

    |prefixCount_M(z,u) - (u/M)*w| <= (32 eta+3 epsilon)*w

for every z and u<=M. The target M and the desired mean are fixed before
choosing this member. This is a finite scalar/cardinality tuning theorem.

## Unbounded powers of two, with prescribed coefficient

For every c,delta>0 and N0 there are k>N0, B subset ZMod(2^k), and a finite
palette P containing B and the full group, such that:

* P is nested;
* for every z and u<=2^k,

      |prefixCount(B,B,z,u)/log(2^k) - (u/2^k)*c| <= delta;

* for every C,D in P, every z, and every u<=2^k,

      |prefixCount(C,D,z,u) - (u/2^k)*actualMean(C,D)|
        <= delta*actualMean(C,D).

The proof starts an old complete palette at coefficient c/8, takes the
largest power of two M<=L, and tunes its member to w=c log M. The log(M)/M
limit provides cardinality capacity. The inequality log L<=2 log M and the
small old sparse start provide the lower cardinality bound.

This is an unbounded sequence of dyadic exponents, NOT a claim about every
sufficiently large exponent. In particular the finite period does not have
to retain a large prime factor. A large-prime-factor obstruction cannot be
used to dismiss all possible finite-palette transitions.

## What still does not follow

Clipping preserves the actual short membership prefix of its source member,
but it selects a smaller modulus from a previously chosen larger finite
source. The existential dyadic theorem does not extend an arbitrary old
palette or a previously chosen natural prefix into a later source. Separate
choices at different dyadic exponents are not shown to agree or to have
controlled mixed counts with one another.

For M much smaller than L the relative error grows like eta*L/M; the new
identity does not give cutoff-independent small-scale control. It therefore
does not establish a compatible infinite chain or reverse the threshold
quantifiers in the finite-prefix compactness criterion. No solution of the
original conjecture is claimed.

## Subsequent same-source period comparison

See ClippedTwoPeriodProgress.md. There is now an exact comparison and
uniform mixed estimate for a repeated short clipping and a fresh longer
clipping of one common source. The shorter pattern's own-period mean has
an explicit period-ratio factor; the result does not provide a fixed-c
infinite transition or an arbitrary-prefix extension theorem.
