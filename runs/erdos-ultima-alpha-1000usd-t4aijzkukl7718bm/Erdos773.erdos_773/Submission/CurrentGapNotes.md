# Current main-gap status

The conjecture is NOT settled. `Spec.lean` is unchanged in the latest
continuation, with exactly one admission at line 2031 for 0 < epsilon <= 1/3.
No submission call has been made.

## Combined-modulus route

Local Sidon constraints do not automatically combine into a global Sidon
constraint. The matching of the two summands may be swapped independently at
different primes. In a Cartesian product this is the elementary rectangle
identity

    (a0,b0)+(a1,b1) = (a0,b1)+(a1,b0).

If one instead imposes a genuinely Sidon condition in the entire CRT group,
the usual square-root cardinality bound in the group size applies. This by
itself does not yield enough integer roots in [1,N]; it does not resolve the
small-root lifting problem. Overlapping moduli or correlation codes would
need a new argument, not an assumption that the local matchings agree.

These are limitations of the attempted route, NOT an upper bound disproving
Erdős 773. No new bound on the actual maximum was obtained in this continuation.

## Other cautions

* Prime roots are not automatically Sidon (see Structure.lean).
* Gaussian factorization parametrizes collisions; it does not eliminate them.
* Translating root sets changes the norm equation, but a shift large enough to
  make every root block Sidon costs a square in scale, giving only exponent 1/2.
* Neither the proved density-zero upper bound nor the primorial upper bound
  supplies a fixed positive exponent loss.
* The position-statistic obstruction is fully verified in
  PositionDigitObstacle.lean; its general higher-moment extension remains a
  mathematical sketch, not an audited Lean theorem.

The next useful advance must be a construction of N^(1-o(1)) roots with Sidon
squares, or a fixed-power upper bound along an unbounded sequence. Further
logarithmic refinements or finite examples alone will not settle the task.

## Latest continuation: permutation-class check

No new main-gap bound or construction was obtained. `Spec.lean` remains
unchanged (SHA-256 917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14),
with the same sole admission at line 2031. The latest compile log is
`/tmp/spec-continuation-check.log` and includes the expected admission warning.

The preexisting exact permutation experiment was run. The class of base-eight
permutations of digits 0,...,7 having inversion count 14 has 3477 members and
33 repeated unordered square sums. One independently checked collision is

    2877252^2 + 5496925^2 = 3386565^2 + 5198648^2
                         = 38494763527129.

The respective base-eight words, most significant digit first, are

    [1,2,7,6,3,5,0,4]
    [2,4,7,6,0,1,3,5]
    [1,4,7,2,6,3,0,5]
    [2,3,6,5,1,4,7,0].

This refutes only that particular permutation/inversion-class construction.
The words do NOT have a common leading digit, a common constant digit, or the
inert-prime Eisenstein condition. Thus the example does not refute all possible
combinations of those additional conditions. No positive theorem for such a
combination was found. This computational observation is not used in the Lean
submission, and no additional obstruction theorem was consolidated there.

Network access to the problem page again failed at DNS resolution.

## Fixed-constant continuation

`FixedConstantCarryObstacle.lean` is now fully verified. It supplies a smaller
20-digit collision family with constant digit exactly 3, positive lower digits
all divisible by 3, leading digit 1, equal full histograms, and digit sum below
B. There is an O(sqrt(B))-height family (with a primitive example), and a
separate family for every B>=3635, B%36=35, including prime bases in that
progression. See `FixedConstantCarryResearchNotes.md` for exact formulas,
parameter restrictions, and limitations. All ten printed axiom audits are
clean. This is another obstruction to a sufficient construction, not a
settlement or a new main-gap estimate. Nothing was added to `Spec.lean`.

## Fractional-capacity continuation

`FractionalSquareSidon.lean` now verifies a near-linear fractional analogue:
weights in [0,1] with every positive square-difference capacity at most one
can have mass N^(1-epsilon) eventually, for every epsilon>0. The uniform weight
N^(-epsilon) works by the existing uniform divisor bound. For indicator
weights, the constraints are proved equivalent to the Sidon condition.
All nonnegative weighted sums of the capacities hold too. All three audits
are clean; see `FractionalSquareSidonNotes.md`.

There is no proved subpower-loss rounding theorem. This does not supply an
actual Sidon subset, and does not settle the conjecture or exclude upper
bounds that use integrality. No improvement of the main-gap bounds was
obtained from localized interval counting. `Spec.lean` remains unchanged.

## Latest rounding check

`FractionalSquareSidon.lean` additionally verifies that lossless rounding is
false: at N=7, feasible weights have mass 13/2 while the actual maximum is 6.
The new theorem `lossless_rounding_fails` has a clean axiom audit. This does not
rule out the subpower-loss rounding needed for the conjecture. No actual
near-linear Sidon construction or fixed-power upper bound was obtained.
The main submission file remains unchanged and admitted at line 2031.

## Augmentation continuation

The exchange approach did not yield a new exponent or a rounding theorem.
The elementary blocked-root count is only O(|S|^2 D), with D a bound on
positive square-difference multiplicities; it does not supply a small
hitting set of old roots for multi-root exchanges. See
`AugmentationResearchNotes.md` for the exact scope and ordered-parameter
normalization. These are research notes, not a new verified main-gap result.
`Spec.lean` was left unchanged and still has its sole admission.

## Amplification continuation

`AmplificationBarrier.lean` now proves that no fixed c>0 can make
M(N^2)>=c*N*M(N) hold at every sufficiently large N. For each c>0 the
inequality fails at arbitrarily large scales. This follows from the existing
quantitative dyadic upper bound by iteration along B^(2^m); both printed
axiom audits are clean. See `AmplificationResearchNotes.md` for details and
scope. This is a restriction on a proposed construction, NOT a disproof of
the original near-linear exponent conjecture. Scale-dependent subpower-loss
amplification is not excluded, but no such construction was found.
`Spec.lean` remains unchanged with its sole admission at line 2031.

## Residue-fiber continuation

`ResidueFibers.lean` verifies a positive within-fiber lemma: the squares of
q*a+r, 0<=a<=q, are Sidon when q>0 and gcd(q,2*r)=1. It also verifies that
Sidon control within each fiber, together with Sidon coarse square residues,
does not by itself control their union. The q=11 check uses
54^2+53^2=10^2+75^2. Both printed axiom audits are clean. See
`ResidueFiberResearchNotes.md`. No near-linear mixed-fiber selector or
fixed-power upper bound was obtained; the main file is unchanged.

## Four-digit checksum continuation

The exact checksum search completed; see `ChecksumResearchNotes.md`. No affine
checksum is Sidon at q=3 or q=5, and none of the 59049 quadratic coefficient
tuples is Sidon at q=3. The base-2 success d=c fails for every q>=3 because
its c=0 slice contains 1,4,7,8. These are screening observations, not a new
main-gap theorem. Reviewing polynomial specialization and the primorial
sieve did not yield the missing construction. `Spec.lean` is unchanged and
still admitted for 0 < epsilon <= 1/3. No submission call has been made.

## Factorization and binary-grammar continuation

No near-linear integral selector was obtained from the product factorization
of square differences. The no-adjacent-ones binary grammar, the even-length
1-run grammar, and the base-four {0,1} alphabet all fail by the exact examples
in `FactorGrammarResearchNotes.md`. These are candidate screens only, not
a conjecture disproof. `Spec.lean` remains unchanged with its sole admission
for 0 < epsilon <= 1/3; no proof submission was made.

## Fixed-power amplification continuation

`PowerAmplificationBarrier.lean` now verifies the stronger barrier for every
fixed real theta<2: no c>0 supports eventual
M(N^2)>=c*N^(2-theta)*M(N)^theta. For every such c,theta the inequality fails
at arbitrarily large scales. This extends theta=1 using the primorial upper
bound and a logarithmic recurrence along B^(2^m). All four main audits are
clean; see `PowerAmplificationResearchNotes.md`. This is not a disproof of
Erdős 773 and does not exclude suitably scale-dependent subpower losses.
`Spec.lean` remains unchanged with its admission at line 2031. The main-file
check is `/tmp/spec-power-amplification-check.log`; no submission was made.

## Distinct-digit specialization continuation

`DistinctDigitCarryObstacle.lean` now verifies a 28-digit carry collision
whose words have no repeated digits, equal full histograms, constant digit
exactly 3, leading digit 1, positive lower digits divisible by 3, and digit
sum below the base. The concrete base 372689 is prime, and the four roots
are pairwise coprime. All four printed audits are clean. See
`DistinctDigitCarryResearchNotes.md` for the identity and precise scope.
This rules out another blanket specialization criterion, not the original
conjecture or every possible permutation class. No positive construction
or improved exponent was obtained. `Spec.lean` is unchanged with its sole
admission; the latest main check is `/tmp/spec-distinct-digit-check.log`.
No proof submission has been made.

## AP-free extraction continuation

`APFreeExtraction.lean` now verifies actual near-linear three-AP-free subsets
of the first N squares, using a reflected-translate averaging lemma and
Mathlib's Behrend bound. The finite bound is
(N/2)*exp(-4*sqrt(log(N^2+1))); the eventual N^(1-epsilon) bound is proved for
every epsilon>0. A separate lemma verifies that nontrivial Sidon collisions
inside such a set have four pairwise distinct values. All three printed
axiom audits are clean. See `APFreeExtractionResearchNotes.md`.

This does not exclude four-distinct-root collisions and is not a settlement
or an improvement of the actual square-Sidon exponent 2/3. Further review of
Gaussian factorization, residue restrictions, short intervals, and digit
specialization did not produce a new main-gap estimate. `Spec.lean` remains
unchanged with its sole admission at line 2031 and SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
The latest main compile log is `/tmp/spec-ap-free-check.log`; the auxiliary
compile and audit log is `/tmp/ap-free-extraction.log`. No proof submission
has been made.

## Growing-moment continuation

The higher-digit modular lifting review did not yield a subpower-loss lift.
A new quantitative obstruction to the growing-moment route is now verified:
`SmallSignJets.lean`, `SignedBlockMoments.lean`, and `GrowingMomentObstacle.lean`.
For every k>=1 there are colliding square roots represented by binary words
of length 4*(k+1)<=L<=64*k^2*(k.log2+1), with all first k positional digit
moments equal. The roots are strictly ordered and hence pairwise distinct.
All main audits are clean; see `GrowingMomentResearchNotes.md`.

The construction uses a pigeonhole signed polynomial V with (X-1)^k|V,
then an explicit borrow-tracking signed-block encoding. The evaluated roots
are common multiples of (3,11,7,9), with multiplier V(16)>0. Therefore this
is NOT a primitive or pairwise-coprime growing-moment counterexample. It also
does not show that every moment class fails. It rules out the blanket
polylogarithmic-moment sufficient criterion, not the original conjecture.

No main-gap exponent bound was improved. `Spec.lean` is unchanged, with its
sole admission at line 2031 and SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
The latest main compile log is `/tmp/spec-growing-moment-check.log`.
No proof submission has been made.

## Moment-congruence continuation

`MomentCongruence.lean` now verifies that a signed polynomial V of degree <D,
with (X-1)^k dividing V and D<2^k, also vanishes at -1. Consequently every
V(2^L) is divisible by three when k>0. For k>=17 this applies to every
signed-jet polynomial of degree <16*k^3. Two such efficient multipliers
cannot be made coprime simply by changing block lengths or polynomials.
The separate binary-jet lemma forces represented roots into one residue
class modulo three, which may be a unit class. All four audits are clean;
see `MomentCongruenceResearchNotes.md`.

This blocks a particular primitive repair of the growing-moment obstruction;
it does not exclude all primitive collisions and does not prove that a prime
moment class is Sidon. No main-gap exponent bound was improved. `Spec.lean`
remains unchanged, with its sole admission at line 2031 and SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
The latest main compile log is `/tmp/spec-moment-congruence-check.log`.
No proof submission has been made.

## Canonical-factor and block-selection review

The square-difference factorization was reviewed again, including canonical
factor-pair selection and coarse/fine root blocks. No compatible near-linear
vertex selector or fixed-power upper bound was obtained. Choosing one
representation of each product is not the same as finding a vertex set all
of whose pairs use those representations; the divisor bound does not supply
that compatibility. Requiring coarse square sums to be separated enough to
absorb all fine errors returns the same 2/3-scale counting tradeoff. No new
combinatorial lemma resolves the overlapping-error cases.

These observations are method analysis only, not newly verified universal
barriers. No auxiliary Lean theorem was added in this continuation, and no
main-gap exponent improved. `Spec.lean` remains unchanged and admitted at
line 2031. The latest compile log is `/tmp/spec-factor-selection-check.log`.
No proof submission was made.

## One-step unit-residue lifting continuation

`UnitResidueLift.lean` verifies q^2 divisibility of the pair-sum difference
for equal-square-sum roots in one residue r modulo nonzero q, assuming
coprimality of q and 2r. A small absolute pair-sum gap then identifies the
unordered root pairs. This extracts the congruence step without index bounds.

The file also verifies a four-distinct-root polynomial family with common
residue 1 modulo q and pair-sum difference exactly -2q^2. For q>=3 the
difference is not divisible by q^3. On the unbounded class
q=9282*t+4641, the modulus is odd and all four roots are pairwise coprime.
Thus those conditions alone do not allow iteration of the lift. No primality
or AP-free claim is made. See `UnitResidueLiftResearchNotes.md` for details.

All five printed axiom audits are clean. Log: `/tmp/unit-residue-lift.log`.
No near-linear selector or fixed-power upper bound was obtained. `Spec.lean`
is unchanged with its sole admission at line 2031 and SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
The latest main compile is `/tmp/spec-unit-residue-check.log`.
No proof submission has been made.

## Subpower amplification equivalence continuation

`SubpowerAmplification.lean` now proves that the exact original conjecture is
equivalent to the eventual bound M(N^2)>=N^(1-delta)*M(N) for every fixed
delta>0. The abstract argument applies to monotone f with f>=1 eventually
and f<=N. It shrinks exponent gaps by a factor 3/4 at each step. A separate
square-root interpolation lemma rigorously extends the estimates from
square indices to all sufficiently large integers. All cardinality facts
for the actual maximum are proved directly, without importing `Spec.lean`.

This is a conditional reduction, NOT a proof of the amplification bound or
of either side of the equivalence. All three main axiom audits are clean;
see `SubpowerAmplificationResearchNotes.md`. The factor-selection review
still did not yield a compatible near-linear root selector. No main-gap
exponent improved.

`Spec.lean` remains unchanged with the sole admission at line 2031 and
SHA-256 917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
The latest main check is `/tmp/spec-subpower-amplification-check.log`.
No proof submission has been made.

## Uniform residue-density continuation

`ResidueDensityLower.lean` now gives a global subpower lower bound for the
density of square residues, and a constant-free lower bound uniform in all
polynomially bounded moduli. Its final theorem proves that for every fixed
epsilon>0, the hypothetical cardinality x=N^(1-epsilon) eventually satisfies
ALL of the basic modular cardinality inequalities simultaneously, even for
arbitrarily large moduli. The large-modulus case uses the first N positive
squares as distinct residues. See `ResidueDensityResearchNotes.md`.

This is only a compatibility result for necessary conditions; it supplies
neither a construction nor a disproof, and excludes no stronger arithmetic
method. All three main axiom audits are clean, with no linter warnings.
Log: `/tmp/residue-density-lower.log`. No main-gap exponent improved.

The conjecture in `Spec.lean` remains unchanged and admitted for
0<epsilon<=1/3. No proof submission has been made.
The main-file check `/tmp/spec-residue-density-check.log` confirms the same
admission and the unchanged SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
A further review of factor-pair selection, affine amplification, and
valuation encodings did not yield a near-linear compatible vertex set or
a fixed-power upper bound; no positive theorem is claimed for those ideas.

## Ordered-defect and local-interval continuation

`OrderedCollisionDefect.lean` verifies the positive even pair-sum defect,
the normalized equation 2t(a+t)=z(z+y), and the exact span identity.
It also proves that the full root interval [L,L+H] has Sidon squares when
H^2<8L+4, including the repeated-middle-root case. A polynomial family
attains the four-distinct-root span bound and shows that the leading
constant 8 cannot be increased uniformly for full intervals. This is NOT
an upper bound for arbitrary subsets, nor a disproof of the conjecture.
See `OrderedCollisionDefectResearchNotes.md`.

All four main axiom audits are clean, with no linter warnings. Log:
`/tmp/ordered-collision-defect.log`. The factor-selection and interval-packing
review did not produce a near-linear compatible selector. No main-gap
exponent improved. Spec.lean is unchanged and admitted at line 2031;
its latest check is `/tmp/spec-ordered-defect-check.log`. No submission
has been made.

## Short-block digit-constraint review

Disjoint blockwise digit moments were reviewed as a possible low-loss
construction. For m binary blocks of length D and k binomial moments per
block, the elementary color count is at most (D^k+1)^(k*m), against
2^(D*m) words. Thus appropriately chosen block parameters allow large
classes. This counting observation does not make any class square-Sidon.
No sufficient carry-control criterion for those classes was proved.

The already verified signed-block collisions can be repeated by multiplying
all four roots by the same block-repetition factor, so repeating a bad block
cannot repair it. This observation concerns particular classes and common
multiples; it is not a primitive obstruction or a claim that every large
block-moment class is bad. No new Lean theorem about block classes is claimed.

Further review of polynomial checksums, root projection from number fields,
and modular lifting supplied no compatible near-linear selector. In
particular, equality of formal polynomial squares still cannot be substituted
for equality after integer evaluation. No new exponent estimate was obtained.
Spec.lean was not modified, and no proof submission was made.

## Primitive difference-multiplicity continuation

`PrimitiveDifferenceMultiplicity.lean` proves unbounded representation
multiplicity even for coprime root pairs, and then strengthens this to
families in which ALL participating roots are pairwise coprime. For every k,
a positive difference has 2^k distinct representations on a pairwise-coprime
set of exactly 2^(k+1) positive roots. The stronger result uses nonzero
determinants of complementary-factor linear forms and an elementary prime
support specialization. The roots are not asserted prime.

This only rules out a constant multiplicity bound from coprimality. There is
no claimed near-linear relation to the largest root, no fixed-power upper
bound on the actual maximum, and no subpower-loss rounding theorem.
See `PrimitiveDifferenceMultiplicityResearchNotes.md`.

Both main audits are clean, with no linter warnings. Log:
`/tmp/primitive-difference-multiplicity.log`. No main-gap exponent improved.
Spec.lean is unchanged and still admitted at line 2031. Latest main check:
`/tmp/spec-primitive-difference-check.log`. No proof submission was made.

## Hypergraph selection review

The possibility of removing the logarithmic loss by exploiting low codegrees
was reviewed. The existing one-round Bernoulli alteration only gives the
proved logarithmic-loss bound. Low codegrees alone have not been converted
here into a stronger selection theorem; a sharper random-greedy or uncrowded
hypergraph argument would require substantial additional proof. No relevant
ready-to-use theorem was found in the available Mathlib sources.

No constant-free N^(2/3) endpoint bound, exponent improvement, or near-linear
construction is claimed. In particular, a hypothetical lower bound
c*N^(2/3) with c<1 would not itself prove the epsilon=1/3 endpoint. The
three-root obstructions would also have to remain controlled in any improved
selection argument.

The main file was not modified, and no incomplete proof was submitted.

## Further specialization review and status check

A renewed attempt to retrieve the current problem page failed because the
host could not be resolved. No updated external theorem or problem status
was obtained.

The dependence of the inert-prime digit constructions on the base residue
was reviewed again. No valid specialization theorem preserving Sidon squares
was proved, including for bases in other residue classes. The absence of a
previous counterexample in a particular residue class is not evidence of a
sufficient construction criterion. No new formal theorem is claimed from
this review, and no main-gap estimate changed.

Spec.lean remains unchanged with its sole admission for 0<epsilon<=1/3.
No proof submission has been made.

## Further selection and construction review

The definitions of `IsSidon` and `Finset.maxSidonSubsetCard` were rechecked in
`FormalConjecturesForMathlib/Combinatorics/Basic.lean`; they have the expected
meaning, including repeated summands. No applicable near-linear extraction
result was found in the available library sources.

Modular residue-fiber selection, short-interval packing, rational rotations,
and polynomial specialization were reviewed again. No new sufficient
construction criterion or fixed-power upper bound was established. In
particular, counting a reduction in residue collision types is not by itself
an improved alteration bound: the collisions between repeated residue fibers
must still be counted and removed. No improved exponent is claimed from that
review. Formal polynomial Sidon identities still cannot be substituted for
integer specialization, and the fractional relaxation still lacks the needed
integral rounding theorem.

No new Lean theorem was added in this continuation. `Spec.lean` was left
unchanged, with its sole admission for 0 < epsilon <= 1/3. The latest main
compilation check is `/tmp/spec-selection-review-check.log`. No incomplete
proof was submitted.

## Rational-base and digit-selection continuation

Rational-base encodings, mixed-radix weights, carry-profile constraints, and
monotone digit classes were considered as possible high-entropy selectors.
No sufficient square-Sidon criterion was proved for any of them. In
particular, the number of available digit words cannot be used as a lower
bound for the Sidon maximum without proving that the selected words avoid
all nontrivial evaluated square-sum collisions. Modular information about
leading or trailing digits alone did not supply that proof. No positive
claim or general counterexample theorem for these candidates is made.

The primitive high-moment gap was also reviewed, without a new result.
Existing common-multiplier moment collisions still must not be called
primitive, and the congruence restrictions still do not exclude common unit
residues. No integral selection theorem, exponent improvement, or disproof
was obtained.

`Spec.lean` remains unchanged, with its original statement and sole import,
and its admission for 0 < epsilon <= 1/3. No proof submission was made.

## Further factorization-selection review

The positive-difference factorization and the existing fractional and
coprimality results were rechecked. No compatible near-linear vertex selector
was obtained. Choosing one representation separately for each difference
does not ensure that every pair of roots in a large selected set uses those
choices. The existing multiplicity bounds therefore still cannot replace
an integral selection argument.

No new lower exponent, fixed-power upper bound, or Lean theorem was proved
in this continuation. `Spec.lean` remains unchanged with the sole admission
for 0 < epsilon <= 1/3. No incomplete proof was submitted.

## Integral bounded-difference selection continuation

`BoundedDifferenceSelection.lean` now proves an actual near-linear integral
selection theorem with relaxed capacities. For every epsilon>0, some fixed
natural g works eventually: there is A subset [1,N], of cardinality at least
N^(1-epsilon), with at most g representations of each positive square
difference. The bound g is independent of N but depends on epsilon.

The proof uses forbidden supports of g+1 equal-difference pairs. Such pairs
need not be disjoint, but their union has at least g+2 roots, which is proved
using injectivity of the larger endpoint and the least smaller endpoint.
Counting these supports and applying Bernoulli alteration gives the result.
See `BoundedDifferenceSelectionResearchNotes.md` for the exact estimates.

The theorem compiles without warnings or admissions, and its axiom audit
contains only propext, Classical.choice, Quot.sound. Log:
`/tmp/bounded-difference-selection.log`.

This does NOT supply multiplicity one or a subpower-loss extraction of an
actual Sidon subset. No exponent for the actual Sidon maximum improved.
`Spec.lean` remains unchanged and admitted for 0 < epsilon <= 1/3. No proof
submission was made.

## Fixed-capacity quantitative continuation

`FixedMultiplicitySelection.lean` now proves that for each fixed g>=1 and
epsilon>0 there are, eventually, actual root subsets of size at least
N^(2g/(2g+1)-epsilon), with at most g representations of every positive square
difference. In particular the capacity-two exponent is 4/5-epsilon.

The construction first takes a near-linear AP-free set of square values.
Equal-difference pairs on that set have disjoint endpoint sets, so g+1 such
pairs use exactly 2g+2 vertices. This improves the forbidden-support size and
gives the finite lower bound p|A|-N^2 K^(g+1) p^(2g+2). The new asymptotic
parameter calculation and subtype-to-natural transfer are fully verified.
See `FixedMultiplicitySelectionResearchNotes.md`.

Both public theorem axiom audits are clean, with no warnings or admissions.
Log: `/tmp/fixed-multiplicity-selection.log`. At g=1 the exponent is still
2/3-epsilon: this is not an improved Sidon exponent or a settlement. No
subpower-loss reduction from bounded capacity to one has been established.
Further digit and arithmetic-structure review yielded no sufficient new
Sidon construction or fixed-power upper bound; no general counterexample
claim about the reviewed digit selectors is made.

Spec.lean was not modified. Its sole admission remains for 0<epsilon<=1/3.
The main check is `/tmp/spec-fixed-multiplicity-check.log`. No proof submission
has been made.

## Further multiplicity-one factorization review

The modular matched-residue equation, rational-rotation parameterization,
short-interval factorization, and possible augmentation arguments were
reviewed with the aim of improving the actual Sidon bound. No valid saving
beyond the established exponent was obtained. In particular, matching low
residues still leaves the mixed quadratic equation between higher digits;
the modular condition alone does not control those collisions. No stronger
construction criterion or general impossibility theorem is asserted.

Growing binary moment constraints and the primitive-collision gap were also
reviewed. The existing congruence results still permit a common unit residue,
and no sufficient moment criterion for primitive or prime roots was proved.
An attempt to obtain updated external problem information again failed DNS
resolution; no external status was established.

No new Lean theorem or exponent improvement resulted from this continuation.
The actual Sidon lower exponent remains 2/3-o(1), and the fixed-g refinement
must not be used with g>1 as if it were Sidon. Spec.lean remains unchanged,
with its original import and statement and its sole admission at line 2031.
No proof submission was made.

## Primitive growing-moment continuation

`PrimitiveGrowingMoments.lean` now closes one previously unresolved auxiliary
gap. For every k>=1 it constructs four distinct positive odd roots with common
gcd ONE, matching first k binary positional moments, and a nontrivial equal
square sum. Their word length is at most 1280*k^4*(k.log2+1)^2. They are not
asserted pairwise coprime or prime. This does not replace the shorter earlier
common-multiplier construction; it gives a primitive polynomial-length version.

The arithmetic family is

    a=1+3u+3v+uv,       b=1+7u+7v+41uv,
    c=1+7u+3v+29uv,     d=1+3u+7v+29uv.

For positive even u<v it has 0<a<c<d<b, a^2+b^2=c^2+d^2, and
29c+29d-a-41b=16. Oddness and the last identity prove the common-gcd assertion.
Two nested signed-block encoders make the moments agree while retaining the
common constant bit 1. Shared factors of the efficient multipliers therefore
do not force a common factor of the evaluated roots.

`SignedBlockMoments.lean` now exports `exists_block_encoder`; the old theorem
is unchanged and still compiles. The new primitive theorem, its quantitative
corollary, and its explicit non-Sidon consequence all have clean audits and no
warnings. See `PrimitiveGrowingMomentResearchNotes.md` and logs
`/tmp/signed-block-encoder.log` and `/tmp/primitive-growing-moments-final.log`.

This refutes a blanket primitive-plus-cheap-growing-moments sufficient
criterion. It says neither that every moment class is bad nor that prime or
pairwise-coprime high-moment selectors have been excluded. It does not settle
Erdos 773 or improve either main-gap exponent. Spec.lean remains unchanged,
with its sole admission at line 2031. The main check is
`/tmp/spec-primitive-growing-check.log`. No proof submission was made.

## Prime growing-moment continuation

Three new clean modules use the verified upper bound to obtain prime-root
obstructions, without needing a prime-producing parameterization:

* WeakSidonExtraction proves that a finite set without a four-distinct-entry
  additive collision contains a Sidon subset of at least a quarter its size.
* PrimeColorCollisions proves finite and eventual monochromatic prime-root
  collision theorems, including a quantitative entropy criterion.
* PrimeMomentCollisions proves four DISTINCT PRIME roots with k equal binary
  positional moments and a nontrivial equal square sum, all below 2^L with

      L = 2^20*(k+1)^2*((k+1).log2+1)^2.

The prime roots are therefore pairwise coprime. There is also an explicit
pairwise-coprimality corollary, a weaker quartic bit-length theorem, and an
assertion for every sufficiently large bit length for fixed k. These are
nonconstructive existence proofs based on prime counting, a color count, and
the existing primorial Sidon upper bound. They are not primality guesses for
roots of the earlier explicit primitive family.

All new theorem audits contain only the allowed three axioms. All modules
compile without warnings or admissions. See
`PrimeMomentCollisionResearchNotes.md` and final logs
`/tmp/weak-sidon-extraction-final.log`,
`/tmp/prime-color-collisions-final.log`,
`/tmp/prime-moment-collisions-final.log`.

This closes the former absence of ANY prime or pairwise-coprime growing-moment
obstruction at polynomial bit length. It does not show that every class fails
or rule out more expensive moment constraints. There is no improved actual
Sidon exponent and no disproof of Erdos 773. Spec.lean is unchanged with its
sole admission at line 2031. The latest main check is
`/tmp/spec-prime-moment-check.log`. No proof submission was made.

## Collision-saving and dense digit-family review

The remaining multiplicity-one problem was reviewed via collision counts,
modular fibers, rational rotations, and high-entropy digit families. No new
Sidon construction or fixed-power upper bound was established.

A useful sufficient intermediate target remains: a near-linear root set with
only N^(1+o(1)) four-distinct-root collision supports. After AP-free extraction,
the existing alteration argument would then retain a near-linear Sidon subset.
The present global bound is instead O(N^2 log N). No stronger bound for a
suitable large moment class was proved. The new prime moment counterexamples
assert the existence of bad classes; they do not supply a collision-count
lower bound excluding such a selection-and-deletion strategy.

Complete-alphabet permutation words (rather than the particular small
histograms in earlier counterexamples) were considered as another
high-entropy candidate. No sufficient criterion was proved, and no general
counterexample for that complete-alphabet candidate was obtained. Formal
polynomial Sidon properties still cannot be transferred to integer evaluation
without controlling carries. No positive claim is made for a previously
untested base residue class.

This continuation added no new Lean theorem and made no main-gap exponent
improvement. Spec.lean remains unchanged with its sole sorry at line 2031.
No proof submission was made.

## Verified low-collision reduction (latest continuation)

`LowCollisionSelection.lean` now formalizes the four-distinct-support target.
For any finite value set A with E such supports, it proves a Sidon subset of
size at least (p|A|-p^4 E)/4. No AP-free hypothesis or Behrend loss is needed:
after four-support alteration, the existing weak-Sidon extraction removes
three-entry progressions at constant cost.

The quantitative missing hypothesis, eventual square-value sets with
|A|>=N^(1-delta) and E<=N^(1+delta) for every delta>0, is proved equivalent
to the unchanged conjecture proposition. The hypothesis itself is not
proved. Effective exponent accounting and a converse finite supersaturation
bound are also verified; see `LowCollisionSelectionResearchNotes.md`.

All seven audits are clean. No actual Sidon exponent improved and no
fixed-power upper bound was obtained. Spec.lean remains unchanged with its
sole admission at line 2031. The main check is
`/tmp/spec-low-collision-check.log`. No proof submission was made.

## Local collision count and local extraction (latest continuation)

Two new clean modules give positive local estimates:
`LocalCollisionBounds.lean` and `LocalSidonSelection.lean`. For four distinct
ordered collision roots in [L,L+H], the positive half-defect t is at most
T=floor(H^2/(8L+4)); the least root, t, and one divisor determine the whole
quadruple. Thus E(L,H)<=C_delta(H+1) T H^(2delta) uniformly. The factor two in
2t(a+t)=z(z+y) is retained.

The square-value four-support count is bounded by this ordered count with
no ordering-factor loss. The resulting local Sidon lower bound is
7(H+1)/(64 max(1,TK)^(1/3)) whenever tau(D)<=K for 0<D<=H^2. Three-entry
obstructions are included via the previously verified weak-Sidon extraction.
All eight audits are clean; see `LocalCollisionResearchNotes.md`.

There is no new global exponent: long intervals still yield only 2/3-o(1),
and the needed mixed-interval collision control remains unproved. Spec.lean
is unchanged and still has its sole admission at line 2031. The main check
is `/tmp/spec-local-collision-check.log`. No proof submission was made.

## Further multiscale review (no new main-gap theorem)

The interval scales were reviewed for a way of summing local collision costs
without counting mixed configurations as if they were internal ones. No such
selection argument or improved global exponent was obtained.

A useful exact diagnostic is the polynomial identity

    a^2+(2a+5t)^2=(a+4t)^2+(2a+3t)^2.

For H>=1, L>=100 H^2, a=L+x with 0<=x<=H, and 1<=t<=H,
the first pair of roots a,a+4t lies in [L,L+5H], and the other two
2a+3t,2a+5t lie in [2L,2L+7H]. They are strictly increasing in that
order. Both separate intervals satisfy the verified full-interval Sidon
criterion, but these parameters give H(H+1) distinct mixed ordered
collisions. The least root and first gap recover x and t, respectively.
The identity was checked by exact symbolic expansion; this explanatory
count has not been added as a new Lean theorem.

This prevents replacing the union's collision count by a sum of its
within-interval counts. It does not prevent a more selective construction:
for example, retaining just one of these two blocks already keeps half the
roots. It is not a fixed-power upper bound or a disproof of Erdos 773.
Avoiding resonant block pairs alone also leaves collisions using three or
four different blocks uncontrolled. No near-linear selector for all these
cases was found.

No source theorem was changed in this continuation. Spec.lean retains the
same hash and the sole admission at line 2031. No proof submission was made.

## Upper-recursion review (latest continuation, no settlement)

A possible disproof via propagation of a finite density defect was examined.
For example, sufficiently strong submultiplicative bounds for the actual
maximum could turn a strict finite loss into a fixed asymptotic exponent
loss. No such recurrence has been proved.

The straightforward residue-fiber descent is invalid. For every odd q>0,
the already verified `ResidueFibers.unit_progression_squares_sidon` applies
with r=1. Restricting its indices to 1<=a<=q gives q Sidon square values
(q*a+1)^2. For q>=7 the UNshifted square values at indices 1,...,q are not
Sidon, since 1^2+7^2=2*5^2. Thus the fiber is not controlled merely by the
unshifted maximum at the number of its indices. This failure does not by
itself refute every possible upper recurrence for the actual maximum; it
refutes the attempted fiberwise justification.

No cross-fiber upper inequality giving a fixed power loss was obtained.
The primorial upper bounds and the previously proved residue-capacity
inequalities remain compatible with the original near-linear assertion.
No new source theorem was added. Spec.lean is unchanged, with its sole
admission at line 2031, and no proof submission was made.

## Bounded-capacity perturbation review (latest continuation)

The already verified fixed-g sets were examined as inputs to a small-height
integer-root perturbation. No conversion from g>1 to g=1 was proved.
For a common affine shift n -> Q*n+1, an equal square sum is equivalent to

    Q*(a^2+b^2-c^2-d^2)+2*(a+b-c-d)=0.

Every old nontrivial collision with zero quadratic defect is broken, since
its linear defect is nonzero. However, new collisions can come from nonzero
quadratic defects. The fixed-multiplicity theorem for the old square
differences does not bound these shifted equations. The known full unit-
progression construction handles Q comparable to the index range, but that
costs a quadratic root-height increase and is not a near-linear construction.
This is an analysis of that route, not a claim that every possible small
perturbation is impossible.

No new source theorem or improved main-gap exponent was obtained. Spec.lean
is unchanged with its sole admission at line 2031. No proof submission was
made.

## Simultaneous affine capacity: positive selection and a strict limitation

Three new clean modules were verified. SimultaneousDifferenceSelection
provides generic finite-family alteration. SimultaneousAffineSquares gives,
for every fixed k and epsilon>0, a single eventual root set of size at least
N^(1-epsilon) controlling positive differences of all affine squares
(qn+r)^2, 1<=q<=N^k, 0<=r<=N^k, with a fixed capacity g(k,epsilon).
The normalization and divisibility/positivity transfer are explicit.

UniversalAffineSidonBound proves that demanding capacity one for ALL shifts
is strictly stronger: if A subset [1,N] has Sidon affine-square images for
1<=q<=4N, 0<=r<=2N^2, then |A|^4<=48(N+1)^3. The proof uses compatible
ordering of root-pair sums and square-pair sums, disjoint interval hulls of
sum fibers, and Cauchy-Schwarz. The near-linear version requiring all
q,r<=N^3 is therefore false. This strengthened negation is NOT a disproof
of Erdos 773. A trusted finite example distinguishes the hypotheses: the
squares of {1,3,4,5} are Sidon, but the shift 2n+1 is not.

See SimultaneousAffineResearchNotes.md for precise scope, public APIs, and
logs. All eleven printed audits are clean and the three modules have no
warnings or admissions. No actual Sidon lower exponent or unshifted upper
exponent improved. Spec.lean is unchanged, with the sole sorry at line 2031.
No proof submission has been made.

## One-shift collision savings and height accounting (latest continuation)

AffineCollisionBounds.lean gives an injective divisor parametrization of
ordered collisions for one unit affine progression qn+r. The positive index
half-defect is q*u, and

  2u(q(a+qu)+r)=z(z+y),
  u<=T=min(floor(N/(2q)),floor(N^2/(8r+4q))).

The divisor argument is <=N^2 independently of q,r. Thus E<=NTK with a
uniform divisor bound K on [1,N^2]. MonotoneSidonSelection.lean generalizes
the previous four-support extraction to increasing images of arbitrary
finite root sets, including three-entry obstructions via weak Sidon.

AffineSidonSelection.lean proves the actual finite lower bound
7N/(64 max(1,TK)^(1/3)), and eventually the uniform bound
N^(2/3-epsilon) q^(1/3) for all 1<=q<=N and gcd(q,2r)=1.
The root height is qN+r. A separate theorem bounds this displayed lower-
bound expression by (qN+r)^(2/3); it does NOT bound the actual maximum.
Hence this positive one-shift saving yields no new global exponent.

All twelve audits are clean; all three modules compile without warnings or
admissions. See AffineCollisionResearchNotes.md for APIs, derivation, scope,
and logs. Spec.lean remains unchanged, including its sole sorry at line
2031. No proof submission was made.

## Full ordinary-alphabet review (latest continuation)

The formal-to-integer polynomial transfer was revisited. No carry-control
construction with near-linear entropy was found. The known inert-prime
Eisenstein counterexamples were distinguished from formal identities.

A different blanket candidate, complete ORDINARY base alphabets, now has a
small verified obstruction in FullAlphabetCarryObstacle.lean. Four base-8
words each use every digit 0,...,7 once, with constant digit 3 and leading
digit 1, but their evaluated roots satisfy

  2254315^2+3437875^2=2272739^2+3425723^2.

The norm-difference polynomial has an explicit factor X-8 and is not zero
formally. The theorem excludes the full fixed-end base-eight family from
being Sidon, not its possible large subclasses or all larger bases. The
lower digits are not all divisible by 3, so this does NOT exclude a complete
alphabet of Eisenstein-allowed digits. See FullAlphabetCarryResearchNotes.md.

All seven audits are clean and the file has no warnings or admissions.
Spec.lean is unchanged with its sole sorry at line 2031. No main-gap exponent
improvement or proof submission resulted.

## Matching local collision powers (latest continuation)

LocalCollisionLower.lean verifies a family attaining the previous local
count's power scale. For L=16K^2T and H=32KT, with K,T>=1, there are at least
KT^2 distinct strictly ordered collisions. Equivalently H^3<=2048 L E(L,H).
The construction uses k in [K,2K-1], t in [1,T], j in [0,T-1], and
m=floor((L+t)/k)+1+j, a=k*m-t, z=2tk, y=m-z. The existing normalized ordered
encoding proves injectivity, and all interval bounds are checked.

A global corollary gives N^2<=9216 E([1,N]) for N>=96. The displayed whole-
interval Bernoulli alteration expression (pN-p^4 E)/4 is consequently at
most 8 N^(2/3), for every p>=0. This is ONLY a bound on that expression,
not on the Sidon maximum or on methods first selecting a low-collision
subset. There is no disproof or new main-gap exponent here.

All five audits are clean, with no warnings or admissions. See
LocalCollisionLowerResearchNotes.md for precise scope and logs. Spec.lean
is unchanged, including its sole sorry at line 2031. No proof submission
has been made.

## Matched-residue continuation

The old full-permutation exact-inversion-count counterexample was rechecked:
it does not fix the end digits. No sufficient theorem for the fixed-end plus
exact-inversion-count variant was established; the finite screens are not
proof of such a theorem.

Two new auxiliary modules compile with clean audits:
`MatchedResidueLifting.lean` and `FullResidueFiberBound.lean`. The first proves
a valid union-of-fibers Sidon criterion using modular square-pair matching and
injectivity of short products. For canonical residues it also proves the
criterion's cardinality ceiling m^3<=4N^2, N=q(H+1). The second supplies a
uniform explicit collision by index 4r+11q+3 inside a full affine fiber.
Consequently a nonempty canonical full-fiber union that is Sidon has H<15q;
with modular pair matching alone its cardinality obeys m^4<=60N^3.

These are ceilings for specified FULL-FIBER CONSTRUCTIONS, not upper bounds
for arbitrary Sidon subsets of squares. Arbitrary partial fibers need not
contain the exhibited indices. No improvement of the actual 2/3-o(1) lower
exponent, no near-linear construction, and no original-conjecture disproof
was obtained. See MatchedResidueResearchNotes.md for definitions and scope.
Spec.lean remains unchanged with the sole admission for 0<epsilon<=1/3.
No incomplete proof was submitted.

## Partial-fiber compatibility and selection continuation

`PartialResidueFibers.lean` now proves an exact criterion under modular pair
matching: the union of arbitrary selected value fibers is Sidon iff each
fiber is Sidon and their actual positive-difference sets are pairwise disjoint.
It also proves exact cardinality for partial affine-square fibers and the
absence of cross-fiber three-term progressions.

`PartialFiberSelection.lean` proves the finite bound

    maxSidon(U) >= p*|U| - p^4*E,
    E = sum_{r<s} |positiveDiffs(V_r) intersect positiveDiffs(V_s)|.

Each unordered residue pair is counted once, and all obstruction supports are
accounted for. There is no factor-four extraction loss because individual
fiber Sidon behavior and modular matching make the entire union AP-free.

An unbounded sparse two-fiber example shows that compatibility is strictly
weaker than short-product separation even on selected gaps. This example has
only four roots and is not an asymptotic construction. Full-fiber ceilings
do not apply to arbitrary partial fibers.

Both new modules compile without warnings or admissions and have clean axiom
audits. See PartialFiberResearchNotes.md for the hypotheses and logs. No
near-linear family with sufficiently small overlap cost was constructed;
no actual main-gap exponent or original-conjecture disproof was obtained.
Spec.lean remains unchanged and admitted for 0<epsilon<=1/3. No incomplete
proof was submitted. A renewed network check again failed DNS resolution.

## Private-modulus partial-fiber continuation

`PrivateModulusPacking.lean` proves a valid divisibility-based way to separate
actual positive-difference spectra, and combines it with the partial-fiber
Sidon union criterion. It also proves the cardinality cost: one index residue
modulo p in A, together with injective affine-square residues modulo p in B,
forces (|A|-1)|B|<=H when A lies in [0,H].

Under modular pair matching, the corresponding pairwise capacity inequalities
force all but one largest fiber to have total size T with

    T^2 <= 4*q*(H+1).

This is proved both for the sum of selected index cardinalities and for the
actual square-value union minus its largest fiber. It applies ONLY to these
selector hypotheses, not arbitrary compatible partial fibers or the original
Sidon maximum. The largest fiber is not newly bounded. Hence this selector
has not supplied an amplification of the existing actual lower exponent.

All seven audits are clean and the new module has no admissions or warnings.
See PrivateModulusResearchNotes.md for exact scope and logs. Finite collision
constant diagnostics did not yield an asymptotic theorem or the epsilon=1/3
endpoint. Spec.lean remains unchanged with its admission for 0<epsilon<=1/3;
no original proof or disproof was submitted.

## Nonuniform partial-fiber continuation

See `WeightedPartialFiberResearchNotes.md`. New clean modules:
`WeightedHypergraph`, `WeightedPartialFibers`, `WeightedSquareExample`,
`TranslatedSquareFibers`. The weighted overlap bound and threshold mass/cost
bounds are proved. A constructed pair of ten-element square fibers has actual
maximum 11, a weighted certificate 95/9, and every uniform expression <=8.
But these fibers are additive translates; the divisor bound proves that
nonzero translated square fibers have only subpower size at root height N.
No favorable near-linear weighted-overlap family has been constructed and no
original exponent has improved. `Spec.lean` is unchanged with one admission.

## Full-fiber weighted overlap continuation

See `FullFiberOverlapResearchNotes.md`. New clean modules:
`FullFiberOverlap`, `FullFiberOverlapCount`, `FullFiberWeightedCeiling`.
Small modular gap matches embed into actual full-fiber common differences,
with explicit endpoints <=10L. Weighted pigeonhole then proves
(K sum p^2)^2 <= q(K sum p^4+2 weightedOverlap), K=L+1. For prime q>=10,
full indices 0,...,q, unit canonical labels and PairMatching, every nonuniform
alteration expression is <=20*(q(q+1))^(2/3). This is a method-expression
ceiling only, NOT an upper bound on the actual maximum or arbitrary partial
fibers. No uniform pairwise overlap lower bound was proved or needed.
The original theorem and its sole admission are unchanged.

## Unequal and shorter full-fiber continuation

See `UnequalFullFiberResearchNotes.md`. Four new clean modules:
`ShortFullFiberOverlap`, `ShortFullFiberWeightedCeiling`, `UnequalFullFibers`,
`AllLengthFullFiberCeiling`. The earlier forced-gap injection now works for
full prefixes 0,...,H with H<=q. Length bins in powers of eight give a 480*N^(2/3)
ceiling for unequal short-fiber certificates, without a logarithmic loss.
Using individual Sidonness (H_r<15q), truncation, and p/3 rescaling extends
this to arbitrary full-prefix lengths with constant 38880, for prime q,
canonical unit residues and PairMatching. If the entire full-fiber union is
Sidon, its cost is zero, giving a genuine two-thirds size ceiling for that
restricted construction. None of these results bounds the original maximum,
arbitrary partial fibers, or arbitrarily shifted index intervals. Spec.lean
and its sole admission are unchanged; no original exponent has improved.

## Exact-inversion digit continuation

`ExactInversionCarryObstacle.lean` is kernel-checked without admissions or
warnings. The four base-nine roots 45611852, 72029084, 57841556, 62633732
are full-alphabet permutations with common leading digit 1, constant digit 5,
and exact inversion count 13. Their squares satisfy a nontrivial equal-sum
identity. The formal norm difference has a factor X-9, verified by `ring`.
This refutes the blanket fixed-positive-end exact-inversion criterion only.

The exact C++ screen checked all base-nine full-permutation classes grouped
by leading digit, constant digit and exact inversion count (67,635,200
unordered square-pair checks). There were three repeated sums, recorded in
/tmp/exact-inversion-base-nine.log. The leading-1, constant-3 classes were
collision-free in this finite screen; nothing asymptotic follows. All 5040
uniform digit relabelings of the positive-end example that would change its
ends to 1 and 3 were tested and none retained the identity. Neither this
finite observation nor the verified collision settles the original problem.
Spec.lean is unchanged with its sole admission.

## Collision codegrees and linearization continuation

See `CollisionLinearizationResearchNotes.md`. Six clean new modules prove a
Gaussian divisor subpower bound, positive sum-of-two-squares representation
bounds, uniform subpower pair codegrees, and the fact that AP-free square
collision edges cannot share three roots. A generic six-vertex-overlap
alteration lemma then produces actual root sets of size N^(4/5-epsilon)
with AP-free squares and LINEAR four-root collision hypergraphs. This is a
relaxed-selection theorem, not an improved Sidon exponent: collisions can
remain, and generic linearity does not supply subpower-loss extraction.
All audits are clean and the modules have built .oleans. The original
Spec.lean statement and sole admission are unchanged; nothing was submitted.

## Controlled linearization continuation

See `ControlledLinearizationResearchNotes.md`. Four new clean modules add a
retained-edge penalty to alteration, giving AP-free linear-collision root
sets B with N^(4/5-epsilon)+N^(-2/5-epsilon)*|edges(B)|<=|B|. Incidence-degree
trimming then yields size N^(4/5-epsilon) and maximum collision degree at
most N^(2/5+epsilon), with AP-freeness and linearity retained. All audits and
builds are clean. Ordinary independent-set extraction still gives exponent
4/5-(2/5)/3=2/3, so no actual original Sidon exponent or endpoint improved.
Spec.lean and its sole admission are unchanged; no proof was submitted.

## Carry-aware parabola lift continuation

`ParabolaSquareLift.lean` is a new clean, audited module. For every odd prime
p it constructs at least (p-1)/2 canonical unit roots below p^2 with square-
pair matching modulo p^2. The high root digit solves the square-lifting
congruence; a half-band restriction on the low square digits removes the
carry ambiguity before using sum-and-square-sum uniqueness over ZMod p.

This is only square-root size at the stated root height. The next full-fiber
step fails even for the actual p=3 lift R={5,7}: 41^2+43^2=7^2+59^2 occurs
inside its full index fibers 0,...,9 modulo 9. Both the exact lifted image and
the non-Sidon union are kernel verified. See ParabolaSquareLiftResearchNotes.md
for scope and logs. No actual main-gap exponent improved, Spec.lean is
unchanged with its sole admission, and no proof was submitted.

## Prime-power full-fiber continuation

`PrimePowerFullFiberBound.lean` extends a restricted ACTUAL full-prefix-family
ceiling to prime powers q=p^k, including even prime powers. For canonical
unit labels with PairMatching, if the WHOLE equal-length full-fiber union
is Sidon, its root and square-value cardinalities satisfy m^3<=1200N^2 and
m<=11N^(2/3), N=q(H+1), without a restriction H<=q. The proof selects a
half-sized unit-gap set in a short interval, obtains injectivity of the
modular product hash from actual Sidonness, then uses truncation and the
previous long-fiber collision bound. All seven audits and the build are clean.

This is not a bound on arbitrary Sidon subsets of such a union, partial
fibers, arbitrary shifted index intervals, or moduli with multiple distinct
prime factors. No new weighted-certificate claim is made. See
PrimePowerFullFiberResearchNotes.md. Spec.lean and its sole admission remain
unchanged; no original exponent improved and no proof was submitted.

## Formal Gaussian construction continuation

`FormalGaussianSidon.lean` now proves the positive formal statement itself:
for P in Z[X] with natDegree(P)<d and P(0)=1 mod 3, the squares of X^d+6P
form a Sidon set in Z[X]. The monic Gaussian polynomial
X^d+3(P+Q)+3i(Q-P) is Eisenstein at 3; its norm factorization identifies
unordered pairs. This is not an integer-evaluation theorem.

`FormalGaussianSpecialization.lean` verifies failure of specialization for
this EXACT family at the prime base 1439. Four admissible degree-18
parameters give monic degree-19 encodings with constant 6 and all lower
coefficients divisible by 6. Their nonzero formal norm discrepancy is
48 X^25(1439-X)(X-1)(X^5-1), but their evaluated squares collide. Evaluation
is injective on the four root values. Both modules and all twelve audits
are clean and built. See FormalGaussianSidonResearchNotes.md.

No near-linear low-collision specialization count was obtained; the original
2/3 lower exponent has not improved. Spec.lean and its sole admission are
unchanged, and no proof was submitted.

## Cubic and all-degree canonical specialization continuation

`CubicGaussianSpecialization.lean` is a new clean, audited module. For every
t>=6, base B=132t, it gives four degree-3 encodings in the EXACT proved
formal Gaussian family, with constant coefficient 6 and strictly increasing
positive lower digits, all multiples of 6 and less than B. The discrepancy
is 24 X^4(B-X). Evaluation has a nontrivial square-sum collision, despite
injectivity on the four root values and formal Sidonness. The bases are
composite and divisible by 3; no primality claim is made.

The separate AllDegrees namespace proves a canonical-digit obstruction in
EVERY degree k+3, k>=0, at every B=132t with t>=7. Its discrepancy is
24 X^(k+4)(B-X). The constants remain exactly 6; every coefficient is in
[0,B), all lower coefficients are divisible by 6, and the roots are positive
and distinct after evaluation. There is no monotonicity claim in this
all-degree extension. See CubicGaussianSpecializationResearchNotes.md for
explicit formulas, algebraic source, and the exact scope.

All eighteen printed audits are clean and the module has a built .olean.
No lower bound on the largest Sidon subfamily follows from these examples;
no original-conjecture proof or disproof was obtained. The arithmetic-sieve
reconsideration also gave no fixed exponent upper loss. Spec.lean remains
unchanged with the sole admission for 0<epsilon<=1/3; the latest main check
is /tmp/spec-cubic-continuation-check.log. No proof submission was made.

## Uniform modular-density and integer-certificate continuation

`QuadraticResidueDensityLower.lean` is a new clean, audited module. For EVERY
positive modulus q it proves q<=2*tau(q)*R(q), where R(q) counts square
residues. The proof uses multiplication kernels in the cyclic additive
group ZMod q, the gcd sum <=q*tau(q), the map (x,y)->(x-y,x+y), and Cauchy.
Combining with the divisor bound gives a uniform subpower lower density.

More decisively, `all_moduli_accept_subpower_card` proves that the exact
existing modular scalar inequality

    M^2 <= R(q)*(M+2*floor(N^2/q)+1)

is satisfied by M=N^(1-epsilon), eventually in N, simultaneously for ALL
positive q. `integer_cardinality_model` gives one INTEGER m between
N^(1-epsilon) and N satisfying every inequality. No modulus restriction is
left in these final statements. This is a method limitation only: no Sidon
set realizing m is constructed, and stronger sieves retaining information
beyond these scalar inequalities are not ruled out.

See QuadraticResidueDensityLowerResearchNotes.md. All eleven audits are
clean and the module has a built .olean. The original IsSidon and
maxSidonSubsetCard definitions were rechecked with no discrepancy found.
No actual lower exponent improved and no original proof or disproof was
obtained. Spec.lean remains unchanged with its sole admission at line 2031;
latest check: /tmp/spec-density-lower-check.log. No proof was submitted.

## Primitive counting and sharper logarithmic lower-bound continuation

Six new clean modules: PrimitiveSquareCollisions, ParityTriangleCount,
PeriodicCollisionWeights, SharpSquareCollisionCount, SquareSupportCounting,
and SharpLogarithmicLowerBound. See SharpCollisionCountingResearchNotes.md.

The ordered four-root collision count is now in exact bijection with
primitive gap parameters ((u,v),(g,w)), and with unordered root supports.
Parity-sensitive triangular lattice estimates, the mod-30 sieve excluding
common factors 2,3,5, and twenty rational ratio bins give the finite bound

    E4(N) <= N^2*((41/500)*(1+log(2N))+244).

In particular eventually E4(N)<=(83/1000)N^2 log N, with 83/1000<1/12.
Here E4 is the cardinality of the actual four-uniform collision hypergraph,
not M(N) and not an ordered overcount.

A new exact-support alteration lemma then proves an ACTUAL improved lower
bound: eventually M(N)>=N/(N log N)^(1/3). This removes the older factor
1/8 but retains the logarithmic loss. No logarithmic independent-set gain
was proved, even epsilon=1/3 remains open in the file, and no exponent above
2/3 was obtained. The six modules have clean audits and built .oleans and
none imports Spec.lean. Spec.lean is unchanged with its sole admission for
0<epsilon<=1/3; no proof submission was made.

## Exact-cardinality controlled sampling continuation

Three more clean auxiliary modules are now built: FixedCardinalitySampling,
SquareProgressionSupports, and ControlledSquareSampling. They give exact-size
weighted finite sampling and progression-free logarithmic-density carriers
with a sharp fourth-order edge-density saving and uniform subpower pair
codegrees. The strongest normalized bound is

    E4(B) N^2 <= (83/1000) |B|^4 log N,
    (1999/2000) N/log N <= |B| <= N/log N.

See ControlledSamplingResearchNotes.md for hypotheses, proofs, and scope.
All audits are clean. These carriers need not be Sidon, and there is no
proved logarithmic-gain extraction theorem or improved main-gap exponent.
Spec.lean is unchanged and still admitted for 0<epsilon<=1/3; no submission
has been made.

The final recheck for this continuation is
`/tmp/controlled-sampling-final-audit.log`: all fourteen printed audits in
the three sampling modules are clean. The main check is
`/tmp/spec-controlled-sampling-check.log`; it retains the original admission
warning. Spec.lean's SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

Mathlib does contain the finite Harris-Kleitman correlation inequality in
Combinatorics/SetFamily/HarrisKleitman.lean. This does not itself supply the
needed sparse-hypergraph logarithmic-gain theorem. No such extraction theorem
was proved in this continuation, and no new arithmetic argument closed the
near-linear selection gap. No speculative extraction constant or unproved
selection hypothesis was added to the main conjecture.

## Random-priority extraction continuation

Five new clean modules are built: ProductCorrelation,
PriorityHypergraphSelection, PriorityIntegralSelection, CaroTuzaFourUniform,
and PrioritySquareSidonLower. All twenty-one printed audits are clean.

The general four-uniform theorem supplies an actual independent set B with

    n^4 <= |B|^3 (6E+n),

without linearity or codegree assumptions. Its proof uses finite-product FKG,
strict random priorities with ties rejected, an integral comparison, and an
explicit Caro--Tuza coefficient recurrence.

The actual square-Sidon lower bound is now improved to

    eventually M(N) >= (5/4) N / (N log N)^(1/3).

This is a leading-CONSTANT improvement, not a new exponent or the endpoint
for epsilon=1/3. The logarithmic loss remains. See
PrioritySelectionResearchNotes.md for proofs and scope. Combined audit log:
/tmp/priority-selection-final-audit.log.

The main conjecture remains unchanged and admitted for 0<epsilon<=1/3.
Main check: /tmp/spec-priority-selection-check.log; SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
No proof submission was made.

## Root-translation amplification review

The next arithmetic review examined translated ROOT sets and the full
quadratic coefficient identity for q*b+a. It produced no valid cross-fiber
selector and no exponent improvement. Root translations must not be confused
with the value translations covered by TranslatedSquareFibers. Coarse-pair
matching still leaves actual positive-difference overlap between fibers.
See RootTranslationAmplificationResearchNotes.md for the scope of this review.
No new formal theorem or main-file change was made in this review, and no
proof submission was made. The strongest actual lower bound remains the
verified (5/4) N/(N log N)^(1/3), with its logarithmic loss.

## Quantitative amplification-loss continuation

The new clean module QuantitativeAmplificationLoss is built and has six clean
axiom audits. For every c>0, arbitrarily large N satisfy

    M(N^2) < c N M(N) exp(-log N/(1024 log log N)).

Thus, for every fixed real a<1, the analogous eventual amplification lower
bound with loss exp(-(log N)^a) is impossible. See
QuantitativeAmplificationLossResearchNotes.md for proof and exact scope.
This is a barrier to specific amplification laws, NOT a negation of Erdős 773.
No new conversion from bounded multiplicity to near-linear Sidonness was found.
Spec.lean is unchanged and still admitted for 0<epsilon<=1/3; no proof was
submitted. The strongest actual lower bound is unchanged, with logarithmic
loss and coefficient 5/4.

## Four-uniform regularization continuation

FourUniformRegularization is clean and built, with eight permitted-axiom
checks. It embeds any four-uniform maximum-degree-D hypergraph with pair
codegrees at most K>=1 into a D-REGULAR one on 4*p copies, where
p<=2*max(D,5). Pair codegrees and all edge-intersection bounds at least one
are preserved. Independent-set density transfers back without further loss.
See FourUniformRegularizationResearchNotes.md.

This is preparatory work for a stronger extraction theorem, not such a
theorem itself. No logarithmic-gain random-greedy estimate has been proved,
and no actual Sidon lower exponent or endpoint improved. The finite-field
residue review found no compatible near-linear partial-fiber construction.
Spec.lean remains unchanged, still admitted for 0<epsilon<=1/3, and no proof
submission was made.

## Greedy states, stopped moments, and configuration tails

Three new modules are clean and built: GreedyHypergraphState,
StoppedGreedyMoments, and GreedyConfigurationTails. All 23 printed audits use
only the permitted axioms. See GreedyStateAndMomentsResearchNotes.md.

The exact greedy state update now tracks residual sizes 2,3,4, closures,
original-edge multiplicities, and the duplicate correction in the first
moment. The stopped process has a proved inclusion bound (t/L)^|S|, weighted
configuration bounds, witness/tail bounds, and extraction of actual reachable
states. Crucially, every such extraction still permits early stopping:
|I|=t OR Q(I)<L. No long-running-time or logarithmic-gain theorem was proved.

Spec.lean is unchanged, with the same admission for 0<epsilon<=1/3. No actual
Sidon exponent or endpoint improved and no proof submission was made.
Combined audit: /tmp/greedy-state-moment-tail-audit.log.
Main check: /tmp/spec-greedy-state-moments-check.log.

## Duplicate errors, witness packing, and common residual neighbors

GreedyOverlapError, GreedyWitnessPacking, GreedyCommonNeighbors, and
GreedyErrorCertificates are now clean and built. The combined seven-module
greedy audit has 47 permitted-axiom checks; GreedyConfigurationTails now
includes markov_bound and has six printed audits. See
GreedyOverlapAndPackingResearchNotes.md for exact hypotheses and scope.

Verified new controls include |overlaps(H)|<=6|H|K, all-prefix duplicate-error
tail 12|H|K(t/L)^4/B, and a generic disjoint-witness packing lemma. Applied to
common residual neighbors, this proves an all-prefix tail

    (9DK(t/L)^3/(k+1))^(k+1)

above threshold 16K^2*k. The proof retains original edge-pair multiplicity;
it checks at most 3DK indexed patterns, witness sizes 3..4, and incidence
at most 4K^2. It does not assume independent witness inclusion events.

A combined finite probability bound below one now extracts an ACTUAL
reachable independent state satisfying both controls at all selected
subsets. However, its conclusion explicitly remains |I|=t OR Q(I)<L.
Early stopping is NOT ruled out. No long-running-time, logarithmic-gain,
endpoint, or near-linear Sidon theorem was obtained. The strongest actual
lower bound remains (5/4)N/(N log N)^(1/3).

Combined audit: /tmp/greedy-overlap-packing-final-audit.log.
Main check: /tmp/spec-overlap-packing-check.log. Spec.lean remains unchanged,
with its sole admission for 0<epsilon<=1/3 and the same SHA-256. No proof
submission has been made. Temporary CheckOverlapError and CheckPacking API
files were deleted.

## Linear-hypergraph global and local drift continuation

Three new clean, built modules: GreedyLinearDrift, GreedyLinearLocal, and
GreedyLinearHigherDrift. Their 33 printed audits use only the permitted
axioms. See GreedyLinearDriftResearchNotes.md and the combined log
/tmp/greedy-linear-drift-final-audit.log.

Verified results now include exact promotions, global drift bounds with
common-neighbor error, exact local incident-edge updates, and increment
bounds while the tracked vertex survives. In a LINEAR original hypergraph,
local two-edge losses equal the common-neighbor count exactly and there is
at most one promotion. Safe-choice local drift is proved for all residual
sizes >=2, including the two-degree correction and the higher-degree error
choose(j,2)*C*d_j(u). Uniform profile bounds remain explicit hypotheses.

No concentration, differential-equation tracking, or long-running-time
theorem was proved. Safe-choice sums do not by themselves construct the
required process that freezes degree values at vertex death. Early stopping
remains unresolved. A bounded-multiplicity review produced neither a new
Sidon conversion nor a general impossibility theorem. No actual Sidon
exponent or endpoint improved; even a logarithmic greedy gain would not
settle the square-specific near-linear gap.

Spec.lean remains unchanged, with its sole admission at line 2031.
Latest main check: /tmp/spec-linear-drift-check.log. No proof was submitted.

## Finite variance-sensitive crossing and greedy-kernel continuation

Four new clean, built modules: FiniteKernelCrossing, FiniteFreedman,
FiniteKernelChoices, and GreedyFiniteKernel. Their 24 printed audits are
clean. See FiniteFreedmanResearchNotes.md and the combined log
/tmp/finite-freedman-greedy-final-audit.log.

A finite adaptive first-crossing theorem now bounds

    Pr[exists n<=T: X_n>=a and V_n<=s]
      <= exp(-a^2/(4(s+b*a)))

under explicit support increment, conditional supermartingale, second-
moment, and compensator hypotheses. It covers all crossing times and has
finite union and actual good-path extraction lemmas. No independence of
successive choices is assumed.

Uniform action pushforwards retain next-state multiplicities. The stopped
greedy step is now identified with a finite kernel. A compatible finite-
memory lift preserves terminal carrier moments and monotone-event first-
hit probabilities, and its paths project to genuine Reach states.

No actual frozen-degree state or its invariants have been implemented yet.
The concrete variance budgets, supermartingale tracking, and exclusion of
early stopping remain unproved. The kernel bridge does not allow arbitrary
extra carrier holds while Ready remains true. No actual Sidon lower bound
or endpoint improved; a logarithmic gain alone would still not close the
square-specific exponent gap. The arithmetic review found no valid new
near-linear selector or disproof.

Spec.lean is unchanged, with its sole admission at line 2031. Latest main
check: /tmp/spec-finite-freedman-check.log. No proof submission was made.

## Concrete recorded process, excursions, and deterministic availability

Seven new clean, built modules now complete the planned finite-memory bridge:
GreedyTrackedState, GreedyTrackedMoments, GreedyTrackedVariance,
GreedyRecordedCrossing, FiniteExcursion, GreedyRecordedExcursion, and
GreedyAvailableProfiles. They total 1360 lines and 49 printed audits. The
updated 11-module finite-kernel/recorded-process audit has 75 permitted-axiom
checks, with no warnings or admissions. See
GreedyTrackedExcursionResearchNotes.md and
/tmp/greedy-tracked-excursion-final-audit.log.

The concrete state records live degrees and bounded last-update clocks,
freezes records at vertex death or guard failure, and NEVER inserts an
extra carrier hold while Ready. Its actual recorded Reach implies Valid;
terminal carrier moments and monotone first-hit bounds agree exactly with
the old stopped process. Actual conditional error drift retains the safe-
choice factor, and useful second moments use promotion/loss variation rather
than horizon times squared maximum increment.

Signed recorded-error crossing bounds now apply under explicit controls.
A critical-excursion theorem only assumes nonpositive mean where X>=0 and
bounds first crossing of a>b by

    (T+1) exp(-(a-b)^2/(4*(sum v + b*(a-b)))).

Finite families and auxiliary carrier-error events can be combined on one
actual avoiding path. Conditional full-run certificates keep guard and
readiness implications explicit; they do NOT prove these hypotheses.

A useful deterministic reduction now tracks availability from local
2-degree profiles in a LINEAR hypergraph:

    Q(I+w)=Q(I)-1-d_2(I,w).

Summing lower/upper degree profiles gives two-sided Q bounds. The theorem
reach_running_profiles obtains this invariant at every reachable running
state from guard-implied prior degree bounds, without circularly assuming
that the guard remains good. Discrete-difference profiles telescope exactly.
A positive terminal lower-Q budget excludes early stops, PROVIDED the
uniform local-degree profile hypotheses and the good-path estimate hold.

No useful quantitative profile, envelope, guard, integrated variance budget,
or numerical sum-of-costs estimate has been instantiated. Hence there is
still no unconditional long-run or logarithmic-gain theorem. No actual
square-Sidon exponent or endpoint has improved. Even a generic logarithmic
gain would not settle the square-specific near-linear exponent gap. The
arithmetic review found no new valid near-linear selector or disproof.

Spec.lean remains unchanged, with its sole admission for 0<epsilon<=1/3 at
line 2031. Latest check: /tmp/spec-recorded-excursion-check.log. SHA-256 is
still 917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
No proof or disproof of the original conjecture has been submitted.

## Explicit trajectory calculus and uniform numerical horizon

Nine further clean, built modules now verify explicit numerical profiles:
GreedyProfileDrift, GreedyProfileVariance, GreedyTrajectoryCalculus,
GreedyEnvelopeCalculus, GreedyScaledTrajectory, GreedyDriftBudget,
GreedyOneStepProfiles, GreedyPhysicalStep, and GreedyUniformHorizon.
They total 1482 lines with 43 permitted-axiom checks. The combined twenty-
module concentration/trajectory audit has 118 checks and no warnings or
admissions. See GreedyNumericalTrajectoryResearchNotes.md and
/tmp/greedy-concentration-trajectory-combined-audit.log.

The mean-field profiles q=exp(-t^3), F2=3*d*t^2*q, F3=3*d^2*t*q^2 and
F4=d^3*q^3 now have checked derivatives, second-derivative bounds, finite-step
Taylor remainders, and slope bounds retaining the necessary q powers.
Growing errors use exp((K-r)*t^3+K*t), r=0,1,2, and the availability envelope
has the essential factor 1/(1+t^2). Their finite growth lower bounds are
proved, not assumed. Explicit degree/common-neighbor/Q boxes yield all six
signed drift inequalities. Deterministic Q propagation through each genuine
choice is also proved.

Uniform scalar conditions are now verified nonvacuously on actual horizons.
In particular, with d=m^4, rho=1/m, K=4000, V>=m^12 and C<=16*m,

    m >= exp(10000*(1+tau)^3), tau>=0

suffices for EVERY one-step scalar condition throughout 0<=t<=tau. Thus the
analytic estimates allow normalized logarithmic-cube-root horizons.
MomentControl constructors now have explicit raw variance numerators, but
integrated budgets and the total simultaneous failure estimate are still
missing. So are the concrete six-test guard/initialization instantiation
and its long-run extraction. No unconditional long greedy run or generic
logarithmic-gain independent-set bound has been proved.

No actual square-Sidon lower bound or endpoint has improved; the strongest
remains (5/4)N/(N log N)^(1/3). A generic logarithmic gain still would not
close the square-specific near-linear exponent gap. No disproof was found.
Spec.lean remains unchanged, with its sole sorry at line 2031. Latest main
check: /tmp/spec-numerical-trajectory-check.log. The same SHA-256 is preserved.
No proof or disproof has been submitted. CheckTrajectoryAPI.lean was removed.


## Concrete greedy extraction and unbounded square-Sidon multiplier

The former guard, initialization, integrated-variance, simultaneous-failure,
and square-transfer gaps are now closed for every FIXED normalized horizon.
Fifteen clean modules (2050 lines, 55 permitted-axiom checks) supply the full
chain. Combined with the previous twenty-module foundation, the audit has
173 clean checks across 35 modules:

    /tmp/greedy-square-gain-combined-audit.log

See GreedySquareGainResearchNotes.md for APIs, constants, and losses. The
actual recorded guard has a noncircular Q invariant; all six drifts and
integrated variance budgets are proved; no early-stop alternative remains.
At d=m^4,rho=1/m,C=16*m,D=m^12, fixed tau, and V<=m^A, the total failure bound
is at most

    m^(2*A)*(1/2)^(m+1)+6*m^A*exp(-m/(68*fixedPenalty(tau))) -> 0.

This gives unconditional independent sets of size V*tau/(2*m^4) in the
regular linear family. Polynomial-size regularization removes regularity,
and exact subtype transport supplies arbitrary ambient finite carriers.
Thus every fixed multiplier of V/m^4 is eventually attained at maximum
degree m^12 and polynomially bounded volume.

IMPORTANT: THE ACTUAL SQUARE-SIDON LOWER BOUND HAS NOW IMPROVED. The strongest
verified theorem is no longer just the fixed 5/4 multiplier. The clean file
GreedySquareSidonLower.lean proves:

    for every c>=0, eventually M(N)>=c*N/(N*log N)^(1/3),

and equivalently M(N)*(N*log N)^(1/3)/N tends to infinity. The proof starts
from logarithmic AP-free sampling, retains the exact collision count in
penalized linearization, trims degrees, and uses p=N^(-1/4),
mu=(log N)^2/(16*N^(1/4)), m=ceil((128*N^(1/4)/(log N)^2)^(1/12)). All rounding,
volume (N<=m^96), and density-transfer losses are proved explicitly.

This is an unbounded leading multiplier, NOT a fixed logarithmic gain or
an exponent improvement. No divergence rate is proved. It still does not
establish the epsilon=1/3 endpoint or any fixed exponent above 2/3, and does
not settle Erdős 773. Quantifying the growing-horizon concentration could
remove a logarithmic loss up to a constant, but would still leave the main
square-specific exponent gap. No new near-linear arithmetic selector or
fixed-power upper bound was found.

Spec.lean remains unchanged with its sole sorry at line 2031. Latest main
check: /tmp/spec-greedy-square-gain-check.log. Same SHA-256:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
The new theorem has not been consolidated into the single main file, and
no proof or disproof of the original conjecture has been submitted.
CheckGreedyAPI.lean was deleted; two clean audit source files were retained.


## Growing horizons: the logarithmic loss is now removed

Six more clean built modules (741 lines, 18 checks) complete the growing-
horizon argument: GreedyHorizonFactors, GreedyGrowingFailure,
GreedyGrowingExtraction, GreedyGrowingSquareCertificate,
GreedyGrowingSquareScales, and GreedySquarePowerLower. The combined audit
now has 191 permitted-axiom checks across 41 modules:

    /tmp/greedy-square-power-combined-audit.log

See GreedyLogGainResearchNotes.md for all constants and loss accounting.
Explicit bounds put every horizon factor below exp(10000*(1+tau)^3).
With the old parameter m=n^2, the total failure estimate is uniformly at most

    n^(4*A)*(1/2)^(n+1)+6*n^(2*A)*exp(-n/68) ->0

for ALL tau>=1 with exp(10000*(1+tau)^3)<=n. Thus the extraction threshold
is independent of tau. Regularization and subtype transfer preserve this
uniformity and give independent sets of size V*tau/(2*n^8) for maximum
degree n^24 and polynomial volume. This is a genuinely growing-horizon
result, not an illicit substitution into a fixed-tau eventual theorem.

THE STRONGEST ACTUAL SQUARE-SIDON LOWER BOUND IS NOW:

    eventually M(N)>=c0*N^(2/3),
    c0=1/(32768*15360000^(1/3)),

and in particular eventually M(N)>=(1/10000000)*N^(2/3). The theorem is
GreedySquarePowerLower.eventual_rational_power_lower. This removes the
logarithmic loss, and is stronger than the intermediate unbounded-multiplier
logarithmic-loss result from the immediately preceding entry.

The square transfer uses n=ceil((128*N^(1/4)/(log N)^2)^(1/24)), not the old
twelfth-root rounding. It proves N<=n^192 and chooses

tau=(log N/15360000)^(1/3),

so the allowed horizon budget is <=N^(1/192)<=n. All root-ceiling bounds,
polynomial volume bounds, and real-power cancellations are checked.

THIS STILL DOES NOT SETTLE THE CONJECTURE. The constant is below one, so it
does not establish the exact epsilon=1/3 statement; no exponent above 2/3
is proved. The remaining issue is square-specific arithmetic selection or
a genuine exponent-improving bootstrap, not a missing generic concentration
argument. No near-linear construction or disproof was found.

Spec.lean is unchanged, with the sole sorry at line 2031. Latest check:
/tmp/spec-greedy-power-lower-check.log. SHA-256 still
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
New results are not yet consolidated into Spec.lean; no original proof or
disproof has been submitted. Growing and combined audit sources are retained.


## Post-power-bound arithmetic bootstrap review

No further exponent improvement or settlement was obtained. The review
focused on partial residue fibers, root/index translations, bounded positive-
difference multiplicity, and carry-aware product coordinates. See
PostPowerBootstrapResearchNotes.md. Modular pair matching and individually
Sidon fibers still do NOT supply the missing actual cross-difference
compatibility. No near-linear capacity-g-to-capacity-one conversion was
proved or assumed. Sum representation bounds must not be confused with
positive-difference representation bounds.

The strongest actual theorem remains GreedySquarePowerLower's explicit
positive-constant N^(2/3) lower bound. No Lean source was changed in this
review; Spec.lean retains its sole sorry and unchanged statement/import.
No proof or disproof of the original conjecture was submitted.

## Sumset-incidence continuation

Three new clean modules, totaling 344 lines, verify the promised C4/sumset
route and an arithmetic obstruction to using its bound for a disproof:

* SumsetIncidence: e^2<=|X|(|Y|^2 K+e) and e<=|Y|sqrt(|X|K)+|X| under a
  common-neighbor bound K, for arbitrary finite bipartite relations.
* SidonInSumset: S Sidon and S subset X+Y imply |S|<=|Y|sqrt(|X|)+|X|;
  also a theorem on the actual maximal Sidon cardinality and a general
  translate-intersection version.
* SquareAdditiveBasis: the existing square-difference divisor bound forces
  every natural basis B with squares(1,...,N) subset B+B to have size at least
  N^(2/3-epsilon), eventually and uniformly over B. Every fixed C*N^alpha
  with alpha<2/3 is eventually strictly smaller than every such basis.

The stronger rectangular result proves, for all natural X,Y covering the
squares, eventually |Y|sqrt(|X|)+|X|>=N^(1-epsilon). Thus neither a balanced
nor an unbalanced sumset cover makes this particular C4/Sidon upper-bound
expression yield a fixed-power disproof. This is a limitation of the
certificate, NOT a lower bound for the actual Sidon maximum (which is
bounded ABOVE by that expression), and NOT a disproof of the conjecture.

See SumsetIncidenceResearchNotes.md for exact scope. All 14 public results
have clean permitted-axiom audits in /tmp/sumset-final-audit.log. No module
imports the admitted Spec theorem. The strongest actual square-Sidon lower
bound is still GreedySquarePowerLower's explicit c*N^(2/3).

Spec.lean remains unchanged with its sole admission at line 2031 and the
same SHA-256. Latest check: /tmp/spec-sumset-continuation-check.log. No proof
or disproof of the original conjecture has been submitted.

## Tight coefficient continuation: actual bound improved

The strongest actual square-Sidon lower bound is now

    eventually M(N)>=(1/8192)*N^(2/3).

API: GreedyTightSquareLower.eventual_power_lower. Two new clean modules,
GreedyTightSquareScales and GreedyTightSquareLower, total 246 lines with eight
new permitted-axiom checks. The combined audit now has 199 clean checks
across 43 modules: /tmp/greedy-tight-combined-audit.log. Audit source:
GreedyTightCombinedAudit.lean.

This improves the previous rational coefficient 1/10000000 by more than
1200. It is an ACTUAL bound for maxSidonSubsetCard of the first N squares,
with all extraction hypotheses discharged, not a relaxed or conditional
bound. The improvement comes from n^24<=(26/25)D once the root scale is large,
the sharper volume bound N<=n^97, and tau=(log N)^(1/3)/100. The existing
UNIFORM growing-horizon certificate is reused and its budget is proved.

See GreedyTightCoefficientResearchNotes.md for all constants and identities.
This still does NOT prove epsilon=1/3, because 1/8192<1, and does not improve
the 2/3 exponent. The endpoint review did not produce an asymptotically sharp
average-degree extraction theorem or a new arithmetic exponent argument.
No general impossibility theorem about refining the method is claimed.

Spec.lean is unchanged, with the sole sorry at line 2031 and the same hash.
Latest check: /tmp/spec-tight-square-lower-check.log. No new result was
consolidated there, and no proof or disproof of the original conjecture
has been submitted.

## Squared private-modulus bootstrap review

No new original-conjecture exponent was obtained. The strongest actual
lower bound remains GreedyTightSquareLower's (1/8192)*N^(2/3).

SquaredPrivateModulus.lean verifies a variant of the private-modulus
selector: roots divisible by p have square values divisible by p^2, so
injective square residues modulo p^2 in the other fiber separate their
ACTUAL positive differences. A finite five-root example verifies that this
can work where injectivity modulo p fails. All six public theorems have
clean permitted-axiom audits; log: /tmp/squared-private-modulus.log.

The exact cost, with the stated index residue-class hypothesis, is

    (|A|-1)^2*|B|<=H^2.

Under modular pair matching, even allowing either direction of this cost
for every pair, the total size outside a largest fiber has sixth power
<=200*(q*(H+1))^4. For actual square fibers the union therefore has size
<=largest_fiber+3*(q*(H+1))^(2/3). The parameter is a root-height bound when
labels are canonical; no canonical-label hypothesis is silently assumed.

This is a limitation of that selector, NOT an upper bound on arbitrary
Sidon subsets or arbitrary compatible partial fibers. No bound on the
largest fiber is asserted. See SquaredPrivateModulusResearchNotes.md for
precise scope and the one-way finite example.

No capacity-g-to-capacity-one conversion or compatible-fiber exponent
bootstrap was found. Spec.lean is unchanged with its sole sorry at line
2031 and the same hash. Latest check: /tmp/spec-squared-private-check.log.
No complete proof or disproof of the original conjecture was submitted.

## Formal-specialization bootstrap recheck

The Gaussian-polynomial route was revisited after the tight-coefficient and
squared-private-modulus work. No new exponent improvement or settlement was
obtained. FormalGaussianSidon proves genuine polynomial Sidonness, but its
exact family has a verified prime-base specialization counterexample.
Unrestricted evaluation cannot be used as a transfer lemma.

Adding a small number of digit invariants or appealing to formal
irreducibility does not discharge the needed quantitative carry estimate.
No near-linear subclass with sufficiently few carry-induced obstructions
was constructed. The existing counterexamples concern particular blanket
criteria; they do not exclude all possible subclasses or carry-aware codes.
No stronger impossibility theorem is claimed in this review.

No Lean source was changed in this continuation. Spec.lean retains the same
import, conjecture statement, SHA-256, and sole sorry at line 2031. The
strongest actual lower bound remains (1/8192)*N^(2/3), proved in
GreedyTightSquareLower. No complete proof or disproof was submitted.
