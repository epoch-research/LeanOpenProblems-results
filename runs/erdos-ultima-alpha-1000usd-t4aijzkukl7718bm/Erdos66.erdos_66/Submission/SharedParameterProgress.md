# Shared-parameter product investigation

## Original task status

The conjecture remains unresolved. `Spec.lean` has not been changed, and no
valid proof or disproof has been submitted.

## New checked results

All files below compile and have built oleans.

1. `WeightedCharacterEnergyExplore.lean` generalizes the translated character
   energy bound to an arbitrary fixed integer weight g with |g|<=1. Averaging
   the fourth additive energy of g(x)*chi(a+x) still gives at most
   4 |F| |U|^2. The weighted character correlation identity has the negative
   term -(sum c_i)^2, so arbitrary signs do not invalidate the bound.

2. `SharedParameterKernelExplore.lean` proves the exact two-factor identity
   for

       sum_(i,j<h) (1+f_i f_j b_(i+j)) (1+g_i g_j d_(i+j)).

   The main term is h^2, not h^4. The three errors use the additive fibers
   of f, g, and the pointwise product f*g. If all three energies are at most
   C h^2 and |b|,|d|<=1, the squared error is at most 18 C h^3.

3. `SharedParameterRootExplore.lean` specializes this to the product of
   quadratic root counts over two fields, with parameters a+i and b+i.
   The same label pair (i,j) is used in both fields. These are counts with
   parameter multiplicity, not yet the representation counts of a set.

4. `IndexedCharacterEnergyExplore.lean` performs the energy calculation on
   INTEGER label fibers i+j=w. It applies to every odd prime p with h<=p,
   avoiding any assumption that the two different fields have the same
   additive fibers. It proves the same 4 p h^2 bound with arbitrary fixed
   bounded signed label weights.

5. `SharedParameterSelectionExplore.lean` selects one pair of translates
   over any two primes p,q>8h (h>0), simultaneously controlling the energies
   of chi_p(a+i), chi_q(b+i), and their product by 24 h^2. Both parameter
   intervals avoid zero and opposite pairs. Consequently the shared weighted
   root count R satisfies, uniformly over both target coordinates,

       (R-h^2)^2 <= 432 h^3.

   Principal theorem: `exists_shared_root_flat`.

Axiom audits in `SharedParameterAxiomCheck.lean` and
`SharedParameterSelectionAxiomCheck.lean` use only `propext`,
`Classical.choice`, and `Quot.sound`.

## What this changes, and what it does not

The earlier statement that product templates multiply their means applies
to CARTESIAN products with independent parameter labels. Sharing labels
avoids that particular multiplication: the weighted two-field main term
remains h^2. This is a genuinely different finite construction.

It is NOT an estimate for integer mixed counts between periods p^2 and q^2.
It is a root count in the PRODUCT of the two finite-field planes. Also,
small energies of the two individual characters alone are not enough;
the product character sequence is essential.

## Finite set conversion (subsequently completed)

**Update:** The conversion and origin repair described below have now been
formalized. See `SharedParameterSetProgress.md` and the theorem
`Erdos66SharedParameterFlatSet.exists_shared_flat_set`. The paragraphs below
record the earlier proof plan; their statements that this finite step is
unchecked are superseded by that update. The infinite step remains open.


For injective nonzero parameter labels in both fields, two distinct product
parabolas meet only at the global origin. Thus their summed graph weight
should be the indicator of their union plus (h-1) times the origin mass.
This suggests an O(h) correction at every nonzero target, just as in the
single-field argument. The generic convolution identity and the connection
to actual set counts have NOT yet been formalized for this product.

At the origin, however, the set count is only 1 whereas the weighted count
is h^2. It must be repaired; this cannot be silently ignored. A possible
repair is a partial auxiliary product parabola paired with its reflection,
with injective projections into each field plane. For a nonzero product
target, at least one component target is nonzero; injectivity of that repair
projection could then reduce intersection counts to the one-field root
bound. This is a proposed proof plan, not a checked theorem.

## Infinite step still missing

No prefix compatibility or intermediate-scale estimate has been obtained.
A k-factor shared-label expansion has one sign product for every nonempty
subset of the factors. The straightforward absolute-value estimate therefore
has exponential dependence on k. Avoiding mean multiplication does not by
itself give a workable infinite recursion with shrinking errors.

An actual solution still needs a compatible construction controlling all
integer targets, or a new logarithmic-scale contradiction. None of these
finite weighted statements can be substituted for `erdos_66`.
