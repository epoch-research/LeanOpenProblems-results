# Squared private moduli and the exponent-bootstrap review

This does NOT settle Erdos 773. No improved actual Sidon exponent or fixed-
power disproof was obtained. The strongest actual lower bound remains
GreedyTightSquareLower.eventual_power_lower:

    eventually M(N)>=(1/8192)*N^(2/3).

Spec.lean is unchanged, including its sole admission for 0<epsilon<=1/3.

## A different private-modulus selector

New module: SquaredPrivateModulus.lean.

The earlier private-modulus selector made one fiber's square values constant
modulo p by restricting its indices modulo p. The variant here uses the
singular residue zero: if the ROOTS are divisible by p, their square VALUES
are divisible by p^2. This can permit more elements in the other fiber,
whose square residues need only be injective modulo p^2.

`separate_fibers` proves that the actual positive-difference sets of

    {(q*k+r)^2 : k in A}, {(q*k+s)^2 : k in B}

are disjoint if

    all k in A are congruent to c modulo p,
    p divides q*c+r,
    k |-> (q*k+s)^2 mod p^2 is injective on B.

No primality hypothesis is necessary: any natural modulus works. The proof
uses root congruence to obtain root divisibility, squares that divisibility,
and invokes the already proved value-modulus separation lemma.

`sidon_union` combines the sufficient rule with modular label pair matching
and individual-fiber Sidonness. It genuinely produces a Sidon union under
its hypotheses; it does not assume arbitrary compatible fibers have this
private-modulus description.

## A finite example where the modulus square matters

`squared_modulus_example` checks fibers

    q=11, r=3, A={0,3},        roots {3,36},
    q=11, s=1, B={0,1,2},      roots {1,12,23}.

The first fiber's square values are divisible by 9. The second fiber's square
residues modulo 9 are 1,0,7, hence injective. Modulo 3 they are 1,0,1 and are
NOT injective. The actual difference spectra are disjoint and the union's
five square values are Sidon.

This is a one-way separation example, not a claim that both fibers admit
all the private data in `sidon_union`. It is not an asymptotic construction.
The finite checks use trusted kernel evaluation; no native_decide is used.

## Exact cardinality cost

If the index sets lie in [0,H], the first fiber pays the residue-class cost

    (|A|-1)*p <= H,

whereas square-residue injectivity in the other fiber gives |B|<=p^2.
Consequently `pair_card_cost` proves

    (|A|-1)^2*|B| <= H^2.

This is a different inequality from the older first-power private-modulus
cost (|A|-1)*|B|<=H. Neither inequality is asserted for arbitrary compatible
fibers without the corresponding modulus hypotheses.

The index residue-class hypothesis is explicit. In particular, the theorem
does not charge this cost to a fiber merely because its roots are divisible
by p when p also divides q. No cancellation of q modulo p is assumed.

## All but one fiber remain at the two-thirds scale

`capacity_tail_sixth` is an abstract finite theorem. Let R be nonempty with
PairMatching q R, q>0. Suppose that for each pair of distinct labels r,s,
AT LEAST ONE of

    (m_r-1)^2*m_s<=H^2,
    (m_s-1)^2*m_r<=H^2

holds. The direction may depend on the pair; a single global orientation
or modulus is not required. Choose a largest fiber r0. Then

    (sum_{s != r0} m_s)^6 <=200*(q*(H+1))^4.

For each nonlargest s, either directional inequality implies
(m_s-1)^2*m_s<=H^2, and hence m_s^3<=4H^2+1<=5(H+1)^2.
The label-capacity bound |R|^2<=2q and an elementary maximum/sum estimate
finish the sixth-power inequality.

`private_union_bound` applies the cost to actual partial index sets and uses
the exact partial-fiber cardinality formula. It yields

    |union_r fiberValues(q,r,B_r)|
       <= |B_r0| + 3*(q*(H+1))^(2/3).

The parameter q*(H+1) bounds the actual roots when labels are canonical
(0<=r<q). The cardinality theorem itself does not need canonical labels and
does not assert that height bound without them.

There is NO restriction on the largest fiber in this theorem. It does not
bound arbitrary Sidon subsets of squares or arbitrary compatible partial
fibers. It shows that this squared-private-modulus strategy cannot supply
a larger-exponent contribution by combining many fibers: beyond the
existing two-thirds scale, the mass would already have to be in one fiber.

## Other bootstrap checks

The existing exact partial-fiber criterion and the affine denominator lower
bound were rechecked. The latter already supplies index cardinality
H^(2/3-epsilon)*q^(1/3) in a single unit affine fiber, but the root height is
qH+r. It cannot be treated as a lower bound at height H. Individually Sidon
fibers still require ACTUAL positive-difference compatibility for their union.

The fixed-capacity results still give 2g/(2g+1)-epsilon at difference
multiplicity g. No capacity-g-to-capacity-one conversion with sufficiently
small loss was proved or assumed. No probabilistic obstruction to such a
conversion has been formalized in this continuation either.

## Verification and main status

All six public results in SquaredPrivateModulus.lean compile without warnings
or admissions. Their axiom audits use only propext, Classical.choice,
Quot.sound. The module imports only clean auxiliary proofs, not Spec.lean.
Its built olean is present.

Build and audit log:

    /tmp/squared-private-modulus.log

Main check:

    /tmp/spec-squared-private-check.log

Spec.lean's sole sorry remains at line 2031; its import and conjecture
statement are unchanged. SHA-256 remains

    917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

No result was consolidated into Spec.lean, and no complete proof or disproof
of the original conjecture was submitted.
