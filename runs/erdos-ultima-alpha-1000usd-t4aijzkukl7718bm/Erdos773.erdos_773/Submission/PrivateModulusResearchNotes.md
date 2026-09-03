# Private-modulus separation for partial fibers

This is NOT a settlement of Erdős 773. Spec.lean is unchanged, with its sole
admission for 0<epsilon<=1/3. No original-conjecture upper exponent or improved
lower exponent has been established. No incomplete proof was submitted.

## Verified sufficient selector

File: `PrivateModulusPacking.lean`
Namespace: `Erdos773.PrivateModulusPacking`

`separate_by_modulus` proves the elementary sufficient rule: if all values in
U have a common residue modulo p, and reduction modulo p is injective on V,
then their ACTUAL positive-difference sets are disjoint. Every positive
U-difference is divisible by p, whereas no positive V-difference is.

`separate_affine_fibers` applies the rule to square-value fibers

    fiberValues q r A = {(q*k+r)^2 : k in A}.

A common index residue in A modulo p makes all its square values congruent.
The other fiber B must have injective square residues modulo p.

`private_moduli_sidon_union` combines this rule with the previously verified
partial-fiber equivalence. Under modular pair matching, individually Sidon
fibers with these private-modulus conditions really do have a Sidon union.
No conclusion about arbitrary Sidon fibers admitting such moduli is assumed.

## Exact cardinality cost

`residue_class_card`: if A subset [0,H] has one index residue modulo p, then

    |A| <= floor(H/p)+1.

The proof injects A into the possible integer quotients by p, checking that
common remainders and equal quotients identify the original indices.

`injective_square_residue_card`: if the affine-square residues of B are
injective modulo p>0, then |B|<=p.

`private_modulus_card_cost` combines them without replacing residue alias
counts by actual collision counts:

    (|A|-1)*|B| <= H.

Thus two comparably sized fibers cannot both be near the full index length
under this sufficient selector.

## Most of the cardinality must remain in one fiber

`capacity_tail_bound` is an abstract theorem. Suppose m_r are natural sizes,
R is nonempty, PairMatching q R holds for q>0, and for every r != s in R,

    (m_r-1)*m_s <= H.

There is a largest fiber r0 for which

    (sum_{s != r0} m_s)^2 <= 4*q*(H+1).

Proof: every non-largest m_s obeys (m_s-1)*m_s<=H, hence m_s^2<=2H+1.
Cauchy--Schwarz and the already verified |R|^2<=2q finish the bound.
This abstract result also covers pair-dependent moduli whenever they provide
the displayed pairwise inequalities; it does not need a single modulus
shared by every comparison.

`private_modulus_tail` derives the hypotheses from actual selected index
sets B_r subset [0,H], common index residues modulo their positive private
moduli, and injectivity of the other fibers' square residues.

`capacity_union_tail` writes the conclusion directly on the ACTUAL union of
square values, using its exact cardinality from PartialResidueFibers:

    (|union_r fiberValues q r B_r| - |B_r0|)^2 <= 4*q*(H+1).

For positive canonical residues, N=q(H+1) bounds the root height. Thus this
selector adds at most 2*sqrt(N) roots outside one largest fiber. The bound
places NO new restriction on that largest fiber. It is not an upper bound
for arbitrary Sidon subsets of squares, and does not follow merely from
compatibility of actual difference sets.

## Scope and remaining target

The sufficient divisibility selector is valid but too costly to supply the
missing amplification from the known 2/3 scale. The less restrictive actual
overlap-cost target in PartialFiberResearchNotes.md remains unproved.
No near-linear partial-fiber family with small enough overlap cost has been
constructed, and no fixed-power upper bound on the original maximum was found.

An additional exploratory calculation checked exact finite counts of ordered
four-root collisions and vertex incidences at N=100,300,1000,3000. This was an
investigation of the constants in logarithmic collision estimates, NOT a
counterexample search or a Lean proof. It did not produce a verified
asymptotic constant, a random-greedy theorem, or the epsilon=1/3 endpoint.
No asymptotic claim is inferred from those finite diagnostics.

## Verification

The module compiles without warnings or admissions; all seven printed audits
use only propext, Classical.choice, Quot.sound. The built olean is available.
Log: /tmp/private-modulus-final.log.
Main check: /tmp/spec-private-modulus-check.log, retaining the original
admission warning and the old harmless linter warnings. Spec.lean hash:

    917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14
