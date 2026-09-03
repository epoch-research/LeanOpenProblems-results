# Residue-class necessary conditions

## Status

The original conjecture is still neither proved nor disproved. `Spec.lean`
is unchanged, with its original `sorry`.

## Checked new files

### `ConvRigidityExplore.lean`

For a real vector f on a finite abelian group G, with sum f=1,

    (f(x)-1/|G|)^4 <= sum_t ((f*f)(t)-1/|G|)^2.

The proof uses the convolution/autocorrelation energy identity, not Fourier
characters. Consequences:

- exact uniform self-convolution forces the vector itself to be uniform;
- convergence of the self-convolution to uniform, with eventual mass one,
  forces coordinatewise convergence of the vector to uniform.

### `ResidueSeriesExplore.lean`

For a summable sequence f, define its pushforward to ZMod m by summing f(n)
over n in each residue class.

- Pushforward preserves total mass and commutes with self/mixed convolution.
- The residue-class sum equals the ordinary subsequence sum at n=k*m+j.
- `log(k*m+j)/log k -> 1` for m>0.
- A sequence asymptotic to c log n has a summable generating series inside
  the unit interval.
- If f(n)/log n -> c, the residue-class generating series satisfies

    push_m(f(n)*r^n)(j) * (1-r)/(-log(1-r)) -> c/m,

  as r approaches 1 from below.

### `ResidueEquidistributionExplore.lean`

For any hypothetical witness A,c with c nonzero:

1. With F_A(r)=sum_{n in A} r^n and
   F_{A,j}(r)=sum_{n in A, n=j mod m} r^n,

       F_{A,j}(r)/F_A(r) -> 1/m.

2. F_A(r) -> infinity as r approaches 1 from below.
3. Every residue class modulo every positive integer contains infinitely
   many elements of A.

The first result follows by normalizing the residue masses to total one,
applying the residue representation-series limit to their cyclic
self-convolution, then applying the finite rigidity estimate.

All oleans were built. `ResidueAxiomCheck.lean` checks the principal theorems
and reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Significance and limitations

These results exclude a construction that permanently retains a nontrivial
residue restriction from an earlier periodic stage. Any viable refinement
scheme must eventually relax old restrictions and redistribute its mass.

This is not a contradiction: ordinary random sparse sets can be uniform in
every fixed residue class. It also does not supply the missing transition
between finite cyclic constructions, nor an asymptotic for ordinary
unweighted residue counts.

Exact Tauberian counting asymptotics and the infinite integer construction
remain unresolved in this formalization.

## Subsequent ordinary-count strengthening

`ResidueCountingExplore.lean` now proves ordinary residue equidistribution:
for each fixed positive m and residue z,

  count(A intersect {n : n mod m=z}, N) / count(A,N) -> 1/m.

It also proves the residue count divided by sqrt(N log N) tends to
2 sqrt(c)/(m sqrt(pi)). This uses a newly proved Tauberian transfer; see
`TauberianProgress.md`. The existence conjecture is still unresolved.
