# Repeated-block calculation and fixed-template obstruction

The original conjecture in `Submission/Spec.lean` remains unchanged and
unsettled. These results are auxiliary and are not a submission proof.

## Checked files

- `RepeatedBlockProfileExplore.lean`
- `FixedTemplateObstructionExplore.lean`
- `RepeatedBlockAxiomCheck.lean`

Both exploration files compile and have current oleans. The two main theorems
were audited and depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Triangular profile

Let `B` be a subset of `ZMod M`, and form the natural-number set obtained by
putting the same low-residue template in each of the first `K` consecutive
blocks of length `M`. If its cyclic self-count at a residue differs from `mu`
by at most `E`, the exact integer count at `q*M+t` is

```
triangle K q * lower M B B t
  + triangle K (q-1) * upper M B B t.
```

The triangular kernel uses integer indices. The formula includes `q = 0`,
where `triangle K (-1) = 0`. Since its consecutive values differ by at most
one and the two carry fibers sum to the cyclic count,

```
|r(q*M+t) - mu * triangle K q|
  <= E * triangle K q + mu + E.
```

In particular, uniformly for every natural target `n`,

```
|r(n) - mu * triangle K (n/M)| <= K*E + mu + E.
```

Main names, namespace `Erdos66RepeatedBlockProfile`:
- `interval_sumRep`
- `triangle_le`, `triangle_neg_one`, `triangle_zero`
- `repeatedBlock`
- `repeated_block_formula`
- `repeated_block_error`
- `repeated_block_uniform_error`

## Fixed-period obstruction

Every hypothetical witness is equidistributed in every fixed modulus, by
the already checked `witness_ordinary_residue_equidistribution`. Therefore
it cannot omit a fixed residue class. Applying this to `binaryBlocks M B D`
shows that **no proper fixed low template `B` works for any high set `D`**.

Main names, namespace `Erdos66FixedTemplateObstruction`:
- `no_missing_residue`
- `no_proper_fixed_template`

This excludes fixed-template repetition or thinning as an infinite solution;
it does not negate the existential conjecture. Allowing a changing template
is essential, and its mixed old/new representation counts are still not
controlled by the existing results.

## Assessment

The triangular calculation supplies a finite integer profile, not a bridge
between distinct low periods. It does not overcome the gap identified in
`TransitionBudgetProgress.md` and `MatchingRepairProgress.md`. In particular,
no suitable base for the superquadratically sparse-exception completion
criterion has been constructed.
