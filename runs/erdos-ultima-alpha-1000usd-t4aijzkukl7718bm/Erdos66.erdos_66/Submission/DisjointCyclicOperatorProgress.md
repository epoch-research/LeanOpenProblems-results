# Disjoint cyclic palettes and a universal natural-number operator

## Original conjecture status

The conjecture remains unproved and undisproved. Spec.lean is unchanged
with its original sorry. No valid proof has been submitted.

## Verified production files

* NestedDifferencePaletteExplore.lean
* UniversalCyclicCoarseExplore.lean
* DisjointBlockOperatorExplore.lean

All compile and have current oleans. DisjointCyclicOperatorAudit.lean audits
18 declarations; its saved log uses only propext, Classical.choice, and
Quot.sound. No production placeholder or new axiom was added.

## 1. Disjoint differences of the old nested cyclic family

For a nested family C_i, let D_i=C_(i+1) minus C_i. These layers are pairwise
disjoint. Their mixed count is the second difference of the old mixed
counts. If the four old errors about mu*a*b are at most E, then

    |r_(D_i,D_j)-mu| <= 4E.

Fix c,tau,delta>0 and a finite color count q. There are arbitrarily large
odd cyclic moduli M, positive mu, and q pairwise disjoint colors P_i with

    |mu/log M-c|<tau,
    |r_(P_i,P_j)(z)-mu| <= delta mu

for EVERY i,j and EVERY cyclic target z. This includes same-color pairs.
The proof applies the existing logarithmically tuned nested family at
precision min(1,delta/(4q^2+1)), then takes its successive differences.

This is an alternative to the curve-mask universal kernel selection: it
provides entrywise cyclic control directly. The color count is fixed before
the modulus. No uniform growing-color threshold is asserted.

## 2. Arbitrary infinite coarse families in a cyclic product

For arbitrary later B,C : Fin q -> Set Nat, exact infinite locality and
nonnegative weighted summation give

    |r_(assembly(P,B),assembly(P,C))(z,n)
       - mu sum_(i,j) r_(B_i,C_j)(n)|
      <= delta mu sum_(i,j) r_(B_i,C_j)(n).

One cyclic P is selected before B,C and all targets. There is no finite
coarse-support assumption or finite list of coarse targets. This theorem
is still in ZMod M x Nat.

## 3. Actual natural-number output, with carries retained

For B : Fin q -> Set Nat define

    active_B(k) = {i : k in B_i},
    w_B(k) = |active_B(k)|,
    C_B(k) = union_(i in active_B(k)) P_i.

The weights are real casts of integers between 0 and q. They are not an
arbitrary real-valued fractional profile.

For any positive outer repetition K, define the ACTUAL subset of Nat

    A_B = blockSet(MK, k -> outerLift(M,K,C_B(k))).

The checked membership formula is

    a in A_B iff there is i such that
      floor(a/(MK)) in B_i
      and reduceDigit(a mod MK) in P_i.

If B and B' agree at all coarse indices through N, their output memberships
agree below (N+1)MK. M,K,P are held fixed in this causality statement.

Put F_B(n)=sum_(k=0)^n w_B(k) w_B(n-k). At every n>0, every t in ZMod M,
and every r in Fin K, the existing exact carry engine gives

    |r_(A_B)(n MK + blockDigit(t,r))
       - mu [r F_B(n) + (K-r) F_B(n-1)]|
      <= mu [K eta+1+eta] [F_B(n)+F_B(n-1)].

The existential theorem chooses M,mu,P BEFORE all later positive K, all
infinite B, and all displayed targets. The two carry terms have not been
replaced by a nonexistent group isomorphism. No root-location assumption
is added.

## What is resolved and what is not

There is now a universal actual NATURAL-number operator for these infinite
coarse inputs. It is no longer appropriate to say that this particular
pipeline only has product-group counts or still lacks its fixed-radix carry
formula.

The operator does NOT create a logarithmically accurate F_B. For disjoint
coarse colors, w_B is simply the indicator of their union; for overlapping
colors it is bounded integer multiplicity. No suitable infinite input
profile with the required shrinking error has been constructed.

Also, the sparse fine support union_i P_i is fixed. Permanently retaining
it as a proper residue restriction is incompatible with the exact witness's
necessary residue equidistribution. Changing K alone does not retire that
restriction. The causality theorem does not compare different M or P.

Thus this closes another finite-to-infinite transfer/carry gap but not the
missing coarse-profile or changing-palette compatibility theorem. No
complete proof or universal disproof of Spec.lean follows.

## Subsequent support audit

See FixedSupportMassProgress.md. The support and the quantitative cost of
additive repairs are now checked for this actual operator. A proper fixed
support cannot be corrected by additions of negligible counting mass.
This is not an obstruction to retaining only a finite old prefix while
changing the palette.

## Subsequent finite-modulus flexibility

See ClippedDyadicPaletteProgress.md. A separate construction now gives
logarithmically tuned, jointly endpoint-prefix-balanced finite palettes at
arbitrarily large power-of-two moduli. Thus a large prime factor is not
intrinsic to finite flatness. It still does not provide the compatible
infinite changing-palette chain required for the conjecture.
