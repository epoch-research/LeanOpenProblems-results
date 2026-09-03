# Mixed finite-family progress

The original conjecture in `Spec.lean` is still unchanged and unproved.
No disproof has been obtained either.

## Completed and checked

1. `AsymmetricRepairExplore.lean`: repaired its one outstanding elaboration
   error. The partial-curve disjointness proof now applies `congrArg Prod.fst`
   before rewriting zero membership.
2. `RectangleRepairExplore.lean`:
   - `gridRows`, `gridCols` and their monotonicity;
   - intersection cardinality `i*j`, preserved by injective images;
   - explicit nonzero injection of `Fin (2*H) × Fin H` into `ZMod p`, when
     `2*H^2 < p`;
   - monotonicity of parabola sets and asymmetric repairs;
   - `exists_mixed_flat_prime_family`.
3. `MixedCyclicThickeningExplore.lean`:
   - mixed versions of the existing exact digit-convolution identities;
   - mixed carry-transfer bound `thickenedSet_error`;
   - monotonicity of thickened sets;
   - `exists_mixed_flat_cyclic_family`.

All relevant oleans were built. `NewFamilyAxiomCheck.lean` and
`FamilyFinalAxiomCheck.lean` verify that the main results depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

## Precise new finite result

For any maximum index H and any lower bound N, there is a prime p>N,
p congruent to 1 modulo 8, and nested sets B_i in (ZMod p)^2, such that for
all 1<=i,j<=H and all targets z,

    |r_{B_i,B_j}(z) - 4*i*j| <= E(i,j) + 10*i + 10*j + 8,
    E(i,j)>=0,
    E(i,j)^2 <= 16*i*j*(i+j).

The rectangle repair achieves the origin count `1+4*i*j`, not `4*i*j`;
the extra 1 is absorbed by the stated error. No false exact equality at the
origin is used.

For any K>0 these give nested cyclic sets C_i modulo (p*K)^2 with main term
`4*K^2*i*j` and error

    K^2*(E(i,j)+10*i+10*j+8)
       +2*K*(4*i*j+E(i,j)+10*i+10*j+8).

This controls every pair of densities in one common period, rather than
only self-convolutions.

## Remaining gap

There is no construction of one subset of the natural numbers with the
claimed asymptotic. In particular, passing between unrelated periods has
not been justified. At the boundary between integer blocks, mixed pairs
can supply almost all the representations, so self-count bounds for each
block separately do not suffice.

Possible further finite step: derive exact integer block formulas. If a
block of length M contains a cyclic set C_k, and n=q*M+t with 0<=t<M,
then integer counts split into lower fibers for block pairs k+l=q and
upper fibers for k+l=q-1. For nested, slowly decreasing C_k, monotonicity
brackets these by sums of full mixed cyclic counts, with endpoint errors.
This would permit density tapering on a finite range, but does not by
itself solve the change-of-period problem.

Other thoughts considered, not established:
- Towers of finite fields can preserve coherent quadratic-character
  parameter families along odd extensions. Encoding their growing
  additive dimension into integers incurs many digit carries; the
  available carry averaging has an unacceptable multiplicative cost.
- Translations of one flat cyclic set have flat mixed counts with one
  another. This does not yet produce transitions between moduli.
- Refining a sparse periodic pattern by permanently retaining its residue
  restrictions cannot make its normalized residue distribution converge
  to uniform. A successful construction would have to relax old residue
  restrictions, not merely add new ones.

## Integer block formulas now completed

`IntegerBlockExplore.lean` was subsequently added and compiled:

- `blockSet M C = {a : Nat | (a : ZMod M) ∈ C (a/M)}`;
- `lower` and `upper` count the two integer carry fibers;
- `lower_add_upper` recovers the full mixed cyclic count;
- `block_formula` is the exact decomposition at `n=q*M+t`, `t<M`;
- `block_brackets` gives upper and lower bounds for antitone blocks,
  in terms of neighboring sums of mixed cyclic counts and one endpoint
  fiber on each side.

`BlockAxiomCheck.lean` verifies the two principal results use only the
allowed axioms. The olean was built.

These formulas allow finite tapering using the mixed-flat families. They
still do not provide a transition to a different modulus.
