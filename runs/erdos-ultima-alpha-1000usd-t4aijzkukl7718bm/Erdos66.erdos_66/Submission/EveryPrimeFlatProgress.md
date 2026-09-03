# Every-prime finite templates

The original conjecture in `Spec.lean` is still neither proved nor disproved.
Its statement and original `sorry` remain unchanged. These are finite-field
results, not a resolution of the natural-number problem.

## New checked pipeline

1. `TranslatedCharacterEnergyExplore.lean`: for any finite parameter set U
   in a finite field F of odd characteristic, averaging the signed additive
   energy over translations a gives

       sum_a energy(chi restricted to a+U) <= 4 |F| |U|^2.

   The proof completes the square in each additive fiber and uses the exact
   two-point quadratic-character correlation identity. It uses no Weil bound
   and does not require selecting a special prime.

2. `CharacterTranslateSelectionExplore.lean`: normalizing each energy by
   |U_i|^2 and minimizing their sum gives one common translation for m selected
   sets with energy <= 8 m |U_i|^2, even after excluding fewer than half the
   field elements. For intervals of maximum length L, all shifts introducing
   zero or opposite parameters lie in a set of size at most 2L. Thus every odd
   prime p>4L admits an admissible common translation.

3. `TranslatedMixedFiberExplore.lean`: transfers the translated energy to
   actual parameter sets. The finite-group mixed-energy inequality and short
   sum/difference supports yield, when the self energies are <= C h^2, C k^2,

       (sum |mixed sum fiber|)^2 <= C h k (h+k),
       (sum |mixed difference fiber|)^2 <= C h k (h+k+1).

4. `AbstractSumDifferenceFamilyExplore.lean`: separates the origin repair
   from the parameter-selection method. It gives simultaneous mixed sum and
   nonzero mixed difference counts for any admissible nested parameter family.

5. `EveryPrimeFlatFamilyExplore.lean`: for positive D, any odd prime satisfying

       p > 8 D H + 1,     p > 2 (D H)^2

   admits nested B_i in (ZMod p)^2, with errors E_ij>=0, for 1<=i,j<=H,

       E_ij^2 <= 32 (H+1) (2Di)(2Dj)(2Di+2Dj+1),
       |r(B_i,B_j;z) - 4 D^2 i j| <= E_ij + 12Di + 12Dj + 8,

   and the same bound for mixed differences at every nonzero z.
   Hence relative error can be made small by choosing D large compared with
   H. Unlike the earlier CRT/Dirichlet construction, this works at EVERY prime
   above an explicit polynomial threshold.

All five files compile. Principal declarations were axiom-audited in
`TranslatedCharacterEnergyAxiomCheck.lean`, `TranslateSelectionAxiomCheck.lean`,
and `EveryPrimeFlatAxiomCheck.lean`; only propext, Classical.choice, and
Quot.sound occur.

## Still missing

This controls families within one prime plane, not interactions between
patterns using different primes. Ordinary cyclic thickening preserves sum
flatness but creates nonzero difference spikes between identical copies.
Neither a compatible infinite integer construction nor a universal
contradiction has been obtained.

## Relative-error corollary

`EveryPrimeRelativeFamilyExplore.lean` now compiles and states the result
without an auxiliary energy parameter. For every eta>0 and maximum level H,
there is a positive integer D such that every prime

    p > max(8 D H + 2, 2 (D H)^2)

admits nested sets B_i (with B_0 empty), and both mixed counts have relative
error <=eta around 4 D^2 i j (differences still exclude zero).

The proof chooses an integer T>max(1,1/eta) and

    D = 1024 (H+1) T^2.

`EveryPrimeRelativeAxiomCheck.lean` audits the theorem.

## Further caution about colored block gluing

Even all-target mixed cyclic flatness among different colors does not by
itself control their natural-number block realization. In the exact formula
`Erdos66IntegerBlock.block_formula`, the lower carry fiber uses colors at
indices k and q-k, whereas the upper carry fiber uses indices k and q-k-1.
The known cyclic bound controls lower(C,D,t)+upper(C,D,t) for ONE FIXED pair
(C,D); it cannot combine these terms when the partner colors differ.

Thus a colored replacement for ordinary thickening would need either
control of the separate carry fibers or an additional averaging identity.
It is not enough just to supply the mixed sum/difference flat templates.
No such transition argument has been proved here.

The additional averaging identity mentioned above is now available for
outer-repeated cyclic templates: see `OuterCarryProgress.md`. This resolves
the separate-carry issue for that specific transfer, not the infinite scale
transition or the repeated-copy difference spikes.
