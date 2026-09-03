# Universal transfer for actual infinite coarse sets and mixed families

## Original conjecture status

The conjecture remains unproved and undisproved. `Submission/Spec.lean` is
unchanged with its original sorry. No valid proof has been submitted.

## Verified production files

* `InfiniteKernelLocalityExplore.lean`
* `UniversalInfiniteKernelExplore.lean`
* `MixedDisjointAssemblyExplore.lean`
* `UniversalPaletteMatrixExplore.lean`
* `InfiniteMixedKernelExplore.lean`

All five compile and have current oleans. `InfiniteUniversalKernelAudit.lean`
audits 25 lemmas/theorems; its saved log reports only propext,
Classical.choice, and Quot.sound. None of the production files contains a
sorry or a new axiom.

## 1. Genuine infinite counts, not a finite-support convention

`Erdos66InfiniteKernelLocality.setPairCount A B z` is the cardinality of

    {x : x in A and z-x in B}.

A natural coarse set B is embedded into the nonnegative integers. For a
finite palette P_i, `infiniteAssembly P B` is the actual infinite union

    union_i P_i x natSupport(B_i).

At a target (z,n), every representing coarse endpoint is in [0,n]. Exact
locality therefore identifies this infinite-set count with the finite
assembly formed from the coarse cuts at n. No cutoff is selected when the
palette is selected; cuts are introduced only in the proof at each target.

`coarse_count_antidiagonal` identifies the coarse mixed count with the
ordinary natural antidiagonal count. In particular `coarse_count_self`
identifies its self-count with Mathlib's `AdditiveCombinatorics.sumRep`.

The former finite universal kernel, relative squared-error, and explicit
accuracy theorems now hold for arbitrary B : alpha -> Set Nat and all
natural targets, with one palette preceding B and every target.

## 2. Universal palette formulation before coarse data

`Erdos66UniversalPaletteMatrix` exposes the same selection as a theorem
about the fine mixed-count matrix itself. Write

    paletteSum(P,omega,K;z)
      = sum_(i,j) K(omega_i,omega_j) r_(P_i,P_j)(z).

For a balanced coloring e:Fin h equiv alpha x Fin m, one disjoint palette
has, for EVERY later real kernel K with |K|<=M,

    [paletteSum-h^2 mean(K)]^2
      <= 2[M(10h+8)]^2 + 32h^3 sum_(x,y) K(x,y)^2.

There is no symmetry assumption on K and no coarse ambient group in this
selection theorem. For nonnegative K, the checked relative squared bound is

    error^2 <= |alpha|^4 [2(10h+8)^2+32h^3] mean(K)^2.

The existing sufficient accuracy condition is unchanged:

    h>=1, epsilon>=0, 680 |alpha|^4 <= epsilon^2 h.

It gives |error| <= epsilon h^2 mean(K), including mean zero.
The field is odd and still must satisfy p>h^2+4h+2.

## 3. Two different coarse families, jointly

`MixedDisjointAssemblyExplore.lean` checks the exact mixed assembly identity
for B and C, not only for B=C, and the corresponding matrix-error transfer.
The coarse sets can overlap, both within and across families; disjointness
is needed only between fine palette members.

`Erdos66InfiniteMixedKernel.exists_universal_infinite_mixed_accuracy` now
chooses one P before ALL later infinite B,C : alpha -> Set Nat and ALL n.
With K_n(x,y)=r_(B_x,C_y)(n), it proves

    |r_(assembly(P,B),assembly(P,C))(z,n)-h^2 mean(K_n)|
      <= epsilon h^2 mean(K_n)

for every fine target z. The mixed K_n need not be symmetric. A squared-error
version is also checked. Separate self-flatness is NOT used as a substitute
for mixed flatness.

`mixed_count_prefix_congr` proves exact causality: agreement of the two
coarse inputs through N preserves all these mixed counts through N, for
a FIXED fine palette.

## Scope and unresolved issue

The earlier restriction to finite coarse sets is now removed. It is no
longer correct to cite finite coarse support or a finite target list as
an intrinsic restriction of this universal fixed-color pipeline.

The construction is still in a product of a fixed finite field plane with
the nonnegative integers. It does not identify product-group addition with
ordinary integer addition without carry control. Its sparse fine support
cannot be retained as a permanent residue restriction in an exact witness.
The fourth-power color cost is retained when the alphabet grows.

Most importantly, neither the self nor the mixed theorem creates an
accurate coarse main term, lets epsilon decrease within one fixed palette,
or compares different palettes/fields at successive integer scales. Fixed-
palette causality is not the missing change-of-scale compatibility theorem.
No infinite natural-number witness or universal logarithmic-order sum
fluctuation obstruction has been obtained.
