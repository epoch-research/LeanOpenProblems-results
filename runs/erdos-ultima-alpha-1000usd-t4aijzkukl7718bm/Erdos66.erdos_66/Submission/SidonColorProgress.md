# Multiscale Sidon-color necessary condition

## Original task status

The conjecture in `Submission/Spec.lean` is still unproved and undisproved.
That file remains unchanged with its original `sorry`. No valid final proof
has been submitted.

## Motivation and result

A possible construction would use roughly sqrt(log N) Sidon-like components
on the prefix below N, hoping that mixed counts supply the logarithmic main
term while self-counts are small. A single-scale cardinality bound does not
rule out that budget. The following checked multiscale theorem does.

`Erdos66SidonColorWitness.witness_requires_logarithmically_many_colors`:

If A is a hypothetical witness with c != 0, then there are delta>0 and K
such that, for every J>=K, every coloring

    col : Nat -> Fin m

of the prefix A intersect [0,4^(2J)) into distinct-positive-difference
classes satisfies

    delta*J <= m.

The coloring may be chosen independently for each prefix. Thus compatibility
of the coloring is not an extra hypothesis. The usual unordered-sum Sidon
condition implies the distinct-positive-difference condition, as separately
checked in `distinctColorDifferences_of_unique_sums`.

Consequently, `sublog_colors_exclude_witness` excludes any proposed set whose
such prefixes admit m(J) colors with m(J)/J -> 0. In particular, the proposed
O(sqrt(log N))-Sidon-component scheme cannot give the desired profile.

This is NOT a disproof of the original conjecture. No hypothesis about a
small Sidon decomposition is present in that conjecture, and no such
hypothesis has been derived merely from its representation upper bound.

## Finite block budget

`SidonColorBlockEnergyExplore.lean`, namespace
`Erdos66SidonColorBlockEnergy`, proves `block_energy_bound`.

Let S be a finite natural-number set colored into m classes with unique
positive differences in each class. Divide the integers into blocks of
width u>0, and let t_b be the occupancy of block b. For ANY selected set B
of blocks,

    sum_(b in B) t_b^2 <= m*|S| + 2*m^2*u.

Proof:

* Within a color, two distinct points in the same block determine a unique
  positive difference less than u. All forward pairs across all blocks
  therefore number at most m*u.
* The ordered same-color, same-block pair count is |S| plus twice the
  forward-pair count.
* Cauchy--Schwarz over the colors gives the stated total occupancy bound.

The file also proves the generic partial squared-fiber sum identity needed
for the occupancy calculation. No Fourier analysis is involved.

## Annular amplification

`SidonColorAnnuliExplore.lean`, namespace `Erdos66SidonColorAnnuli`, applies
the block budget with u=4^J to the J annuli

    [4^j,4^(j+1)),  J<=j<2J.

If every annulus has squared mass at least a^2*4^j*J, then

    a^2*4^J*J^2 <= 3*m*|S| + 6*m^2*4^J.

If also |S|<=b*4^J*J, cancellation gives

    a^2*J^2 <= 3*b*m*J + 6*m^2.

For a>0 and b>=0 this forces

    min(1, a^2/(3*b+6))*J <= m.

Principal names:

* `annular_color_budget`
* `color_quadratic_bound`
* `linear_bound_of_quadratic`

## Application to a hypothetical witness

`SidonColorWitnessExplore.lean` uses the previously checked Tauberian profile

    count_A(N)/sqrt(N log N) -> 2*sqrt(c/pi).

Along N=4^k, the normalized count

    count_A(4^k)/(2^k*sqrt(k))

has a positive limit D. Eventually it lies between 3D/4 and 5D/4. Subtracting
neighboring endpoint bounds gives annular mass at least

    (D/4)*2^j*sqrt(j).

This supplies the finite annular theorem with a=D/4 and b=5D/2, yielding the
positive linear-in-J color bound above.

## Verification

All three source files compile and have current oleans:

* `SidonColorBlockEnergyExplore.lean`
* `SidonColorAnnuliExplore.lean`
* `SidonColorWitnessExplore.lean`

`SidonColorAxiomCheck.lean` audits the main results. Only `propext`,
`Classical.choice`, and `Quot.sound` occur.

## What remains missing

This closes off the specific small-Sidon-component proposal; it does not
exclude a more complicated construction with many colors or no useful
Sidon decomposition. The missing infinite construction or universal
logarithmic-order contradiction for the original conjecture remains open
in this development.
