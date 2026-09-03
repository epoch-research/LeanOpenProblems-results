# Finite palette completion at a logarithmic sparse scale

## Original task status

Erdős 66 remains unresolved. `Submission/Spec.lean` is unchanged and still
contains its original `sorry`. No proof or disproof has been submitted.

## Checked production files

1. `FinitePaletteGeometryExplore.lean`
2. `DensePaletteStepExplore.lean`
3. `DensePaletteCompletionExplore.lean`
4. `DenseCyclicPaletteCompletionExplore.lean`
5. `OddLogTuningExplore.lean`
6. `UniformMixedCyclicRelativeExplore.lean`
7. `LogarithmicMixedFamilyExplore.lean`
8. `LogarithmicCompletePaletteExplore.lean`

All compile, have built oleans, and contain no sorries. Principal declarations
pass `DensePaletteCompletionAxiomCheck.lean` and
`LogarithmicCompletePaletteAxiomCheck.lean`, using only propext,
Classical.choice, and Quot.sound.

## The finite chain is now complete

`Erdos66DensePaletteCompletion.exists_complete_palette` takes a finite nested
eta-flat palette P0 with largest member C0 and a common lower cardinality s.
Write M=|G|, and assume doubling is injective. Let 0<eta<=1, 0<g<=1/4,
delta>0, and 32 delta<=eta g. The fixed initial conditions are

    32 <= eta g |C0|^2/M,
    v <= s |C0|/M,      v <= |C0|,
    2 ((M+2)M+1) exp(-delta^2 v/8) < 1.

Then there is a finite palette P extending P0 such that:

- P is nested by inclusion;
- every pair has relative mixed-count error <=eta about |C||D|/M;
- P contains the full group;
- |P|<=M+1;
- for every real x with |C0|<=x<=M, some D in P satisfies

      x <= |D| <= (1+4g)x.

Thus the same tolerance survives the WHOLE densification, not just one step.
The conditions do not have to be re-assumed at an unknown iteration length.

### Finite maximality proof

Any nested palette has injective cardinality map, hence at most M+1 members.
A maximum-cardinality member contains all its other members. Consider ALL
finite palettes extending P0 with nesting, flatness, the lower size bound,
and the indicated multiplicative coverage wherever the palette already
reaches. This is a finite universe, so choose one of maximum cardinality.

If its largest member C has |C| >= (1-g)M, append the full group exactly.
Otherwise set the expected new cardinality to b=|C|/(1-g), using

    theta=(b-|C|)/(M-|C|).

The previously checked dilution theorem gives a new B containing C,
strictly larger in cardinality, with the same flatness tolerance and
|B|<=(1+4g)|C|. All old members are contained in B. The initial lower means
still apply, while |P|<=M+1 bounds all concentration tests. Appending B
preserves the coverage condition and contradicts maximality.

This is ordinary FINITE maximality, not an application of Zorn's lemma to
the non-closed asymptotic upper-bound class examined in older work.

### Cyclic version

`exists_complete_cyclic_palette` takes delta=eta g/32 and v=s|C0|/M. Its
explicit concentration condition is

    8192 log(2((M+2)M+1)) < eta^2 g^2 s|C0|/M.

It applies to odd M and retains the existing cyclicCount/actualMean notation.

## Unconditional logarithmic sparse starting levels

`Erdos66LogarithmicCompletePalette.exists_logarithmic_complete_palette`:

For c,tau,eta,g>0, eta<=1, g<=1/4, it chooses a positive integer H BEFORE
an arbitrary lower modulus bound N0. Then it finds an odd M>N0, a positive
real mu, a nested family C_i, and a complete palette P such that

    |mu/log M-c| < tau,
    C_0 is empty,
    |r(C_i,C_j;z)-mu i j| <= eta mu i j     for i,j<=H,

and P contains every C_i for 1<=i<=H, is nested, is eta-flat about actual
cardinality means for EVERY pair, contains the full group, and has at most
M+1 members. For every x in [|C_H|,M], P has a member with size in
[x,(1+4g)x].

**The multiplicative coverage conclusion starts at C_H, not at C_1.** The
old sparse levels below C_H remain the discrete integer-index family.

### How the concentration threshold is met

Choose H with

    H > max(1, 200000/(eta^2 g^2 c)).

The old nominal error is chosen smaller, sigma=min(eta/4,1/4), so conversion
to actual means costs no more than eta. For sufficiently large M,

    mu >= (c/2)log M,
    |C_1||C_H|/M >= mu H/2 >= (cH/4)log M.

The logarithmic test count is at most 5 log M, so the chosen H pays the
entire completion threshold. The self-mean condition follows by choosing
M sufficiently large. No limiting coefficient of the original conjecture
is allowed to grow with M here: c is fixed first.

The mixed family is obtained at every sufficiently large prime, with freely
variable coordinate thickness. The odd thickness

    oddThickness(d,p) = 2 floor(sqrt(log p/d)) + 1

satisfies

    (d/2) oddThickness(d,p)^2 / log((p oddThickness(d,p))^2) -> 1.

Taking d=8D^2/c gives the desired nominal mean mu=4D^2 K^2. The modulus is
odd because both the chosen prime and K are odd.

## Remaining obstruction

This completes a finite density-retirement tool, not the integer scale
transition. The palettes at different moduli are independently chosen.
The theorem does not preserve an already accurate natural-number prefix,
control mixed counts between unrelated periods, or provide the required
inhomogeneous lower profile through every intermediate scale.

In particular, placing a dense/full residue member in an actual integer
block has a real representation cost. Its mass cannot be treated as if it
were a sparse member. The existing outer-carry transfer can control carry
fibers for a palette within ONE period, but does not supply a schedule for
changing that period. No such schedule or universal contradiction was
proved in this pass.

### Subsequent integer-placement check

`PalettePlacementCostExplore.lean` now formalizes the placement restriction;
see `PalettePlacementCostProgress.md`. In particular, even the sparse starting
member C_H cannot be placed as one full block at a<=M^d under an envelope with
coefficient C if (1-eta)c0 H^2>2Cd and mu>=c0 log M, for sufficiently large M.
The limitation is therefore not confined to the palette's dense endpoint.
This remains a restriction on literal block placement, not a disproof of
Erdos 66.
