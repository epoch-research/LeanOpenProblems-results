# Multiplicative rows: checked identities, not a witness

`MultiplicativeRowsExplore.lean` and `MultiplicativeNaturalRowsExplore.lean` compile.
Eight principal declarations in `MultiplicativeRowsAudit.log` use only the allowed axioms.

For a finite parameter set U in a field, the row at height y is
`{(u+a)/(y+1)-a : u in U}`, or empty if y+1=0.
Its first row is exactly U. Every nonsingular row has exactly |U| points.
Both facts hold for each fixed a; no averaging or extra admissibility is needed.

The mixed target equation is
`(z+1)u+(y+1)v=(y+1)(z+1)(t+2a)-a(y+z+2)`.
The filtered-row identity retains any prescribed endpoint predicate. For equal
heights it reduces to an ordinary old sum count.

For natural numbers written in base p, `natural_formula` includes both carries,
using the appropriate two row heights and the lower/upper endpoint restrictions.
`natural_representation_prefix` preserves the old first-block representations.
`prefix_mass_before_singular` proves exact mass sum_{k<N}|U_k| for N<p.

No asymptotic estimate for the weighted mixed counts is proved. Old self-count
flatness does not imply their flatness. Constant parameter sets give the wrong
mass at large heights; tapering the parameter sets requires new estimates.
Keeping all rows also introduces central symmetry and a large full-group peak.
The original Spec.lean has not been changed.

Lean note: natural binders in residue sums must be explicitly pinned when
needed; visually identical filter cardinalities may also differ in Decidable
instances. The final proofs use finite-set extensionality and explicit
sum-congruence, not any changed definitions or statements.

## Reflected-row obstruction (now checked)

`MultiplicativeReflectionExplore.lean` compiles. Its six principal declarations
are audited in `MultiplicativeReflectionAudit.log`, with only allowed axioms.
Define

    T = sum_{k=0}^{p-2} |U_k intersect U_{p-2-k}|.

At reflected heights k and p-2-k, the same parameter u gives a spatial sum
of -2a modulo p. Tracking the ordinary carry proves

    T <= r_A((p-2)p+val(-2a)) + r_A((p-1)p+val(-2a)).

Both targets lie below p². Consequently some n<p² has T<=2r_A(n).
For any V contained in every U_k for k<N, with N<=p-1,

    (2N-(p-1))_+ |V| <= T.

Thus a cap r_A(n)<=B for every n<p² implies

    (2N-(p-1))_+ |V| <= 2B.

In particular a nested, nonempty taper cannot keep substantially more than
half the field's rows while respecting a logarithmic cap. It is not enough
to remove the singular row or merely to avoid the fixed parameter -a.
Stopping before half the rows avoids this particular argument, but supplies
no mixed-count asymptotic or compatible extension.

These are obstructions to a specific construction, not a disproof of the
original existential conjecture. Every arbitrary natural set can be written
rowwise using suitable U_k; the extra overlap or nesting assumptions need
not hold for those parameter sets.
