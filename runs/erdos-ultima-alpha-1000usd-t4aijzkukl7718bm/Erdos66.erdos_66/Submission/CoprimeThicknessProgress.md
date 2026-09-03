# Mixed compatibility for coprime coordinate thicknesses

## Status and verification

The original conjecture in Spec.lean remains unresolved and unchanged.
Six new production files compile, with current oleans:

1. RectangularRadixExplore.lean
2. RectangularCarryAverageExplore.lean
3. CarrySplitFibersExplore.lean
4. CoprimeThicknessExplore.lean
5. CoprimeThicknessGeometryExplore.lean
6. UniformCoprimeThicknessExplore.lean

CoprimeThicknessAudit.lean audits 17 principal declarations. All use only
propext, Classical.choice, and Quot.sound. There are no placeholders or new
axioms in these production files. CrossThicknessChecks.lean and
CrossThicknessChecks2.lean are name-search scratch files with failed checks;
do not blanket-build them.

## The actual cyclic construction

Let p,K,L be positive, p coprime to K*L, and K coprime to L. Write

    Q = p*(K*L),     M = p*Q.

A rectangular radix equivalence identifies ZMod M with a lower digit in
ZMod p and an upper digit in ZMod Q. Its subtraction formula includes the
usual lower-digit borrow, exactly. CRT identifies the upper digit with
ZMod p times ZMod K times ZMod L.

For plane sets B,C, the left set tests

    (low, high_p - val(high_K)) in B,

and the right set tests

    (low, high_p - val(high_L)) in C.

These are actual finite subsets of ZMod M, not weighted multisets.
Their exact cardinalities are

    |leftSet(B)| = K L |B|,       |rightSet(C)| = K L |C|.

Hence their actual mixed mean in ZMod M is

    K L |B| |C| / p^2.

## Exact identification with the earlier coordinate thickenings

For EVERY natural n, membership in the left set is equivalent to

    (n mod p, K * floor(n/(pK)) mod p) in B.

Thus it is exactly the earlier thickenedSet(p,K,verticalPreimage(K,B)),
where verticalPreimage(k,B) contains (x,y) iff (x,k*y) belongs to B.
The right set is the analogous L-thickening of C. This identification is
not restricted to one initial period. The vertical rescaling is essential;
the theorem does NOT assert compatibility for arbitrarily unrelated plane
sets or for unrescaled old templates.

## Mixed count and boundary-strip error

After CRT reindexing, the mixed count at lower/upper digits (t,s) is

    sum_(i mod K,j mod L)
      [beforeCount(B,C,t,s_p-i.val-j.val)
       + afterCount(B,C,t,s_p-i.val-j.val-1)].

beforeCount restricts the first endpoint to x.val<=t.val; afterCount uses
x.val>t.val. The borrow is retained until this point.

For scalar functions f,g, summation in i gives the exact telescoping identity

    sum_(i<K) [f(z-i)+g(z-i-1)]
      = sum_(i<K) [f(z-i)+g(z-i)] + g(z-K)-g(z).

If |f+g-mu|<=E and 0<=g<=mu+E, the rectangle therefore has error at most

    K L E + min(K,L)(mu+E).

Consequently, if all plane mixed counts of B,C have mean mu and error E,
then at EVERY cyclic target

    |r_(leftSet(B),rightSet(C)) - K L mu|
      <= K L E + min(K,L)(mu+E).

The carry cost is boundary-sized, not area-sized.

## Unconditional uniform family

`every_prime_coprime_thickness_family` fixes eta in (0,1] and a finite level
bound H, then chooses D,K0. For every prime p above the existing explicit
plane-family threshold it selects ONE nested plane family B_i BEFORE the
thicknesses are chosen.

For every later positive K,L with p coprime to KL, K coprime to L, and
max(K,L)>=K0, all mixed level pairs i,j<=H satisfy

    |r_mixed(z) - 4 D^2 K L i j| <= eta * (4 D^2 K L i j)

in their common cyclic modulus p^2 K L, at every target. No separate
self-flatness is used as a substitute for mixed flatness. The theorem controls
mixed counts of the displayed distinct-thickness patterns; self-thickening
bounds remain available from the earlier same-thickness transfer.

## Still missing

This is compatibility across coordinate thicknesses over ONE common prime,
not between different fields. Varying thickness alone does not make the
underlying plane density tend to zero. No infinite change-of-prime chain,
short-interval estimate uniform down to a fixed initial cutoff, or compatible
finite-prefix construction has been proved.

A possible next finite step is endpoint-prefix transfer and integer assembly
for these common-prime different-thickness patterns. The generic outer-lift
prefix engine can be applied in their common period, but doing so is still
not the compactness hypothesis required by the original conjecture.

No proof submission has been made, and Spec.lean still contains its original
sorry.
