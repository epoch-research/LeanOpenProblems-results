# Centered mixed-energy bound

## Status

`Submission/Spec.lean` is unchanged and still contains the original `sorry`.
The conjecture has not been proved or disproved. No proof has been submitted.

`CenteredMixedEnergyExplore.lean` compiles and has a current olean. The main
results were audited in `CenteredMixedEnergyAxiomCheck.lean`; they depend only
on `propext`, `Classical.choice`, and `Quot.sound`.

## Main result

For real weights f,g on a finite abelian group G of cardinal M, put

```
mean(f,g) = (sum f)*(sum g)/M
V(f,g) = sum_z (conv(f,g)(z)-mean(f,g))^2.
```

The checked result is the **centered** interpolation inequality

```
V(f,g)^2 <= V(f,f)*V(g,g).
```

It follows by writing V(f,g) as the inner product of the two centered
correlations, then applying Cauchy--Schwarz. This is stronger for nearly
constant self-convolutions than the older uncentered energy inequality.

If the self-convolutions of f,g have uniform errors E,F around any centers,
then

```
V(f,g) <= M*E*F.
```

In particular, for finite sets B,C, the number of residues whose mixed count
differs from |B|*|C|/M by more than delta satisfies

```
number_bad * delta^2 <= M*E*F.
```

No common algebraic construction of B,C is required, but they must be viewed
on the same finite group. This is an L2/counting estimate, not pointwise mixed
flatness and not a transfer across short intervals of unrelated periods.

## Limitation of the generic certificate

For a sparse template B with |B| <= M/2 and exact self mean mu=|B|^2/M,
the previously established variance floor gives the checked consequence

```
mu <= 4*E^2.
```

Thus the numerical Chebyshev certificate at relative tolerance delta obeys

```
M*E^2/(delta^2*mu^2) >= M/(4*delta^2*mu).
```

At logarithmic mean this generic certificate is at least of order M/log M,
far above the exceptional-set size sufficient for the existing sparse repair
engine. This does **not** lower-bound the actual exceptional set: a particular
mixed pair can have much better behavior than this certificate proves.

## Main names

Namespace `Erdos66CenteredMixedEnergy`:
- `mixedMean`, `centeredEnergy`, `centeredCorr`
- `centeredEnergy_eq_corr_inner`
- `centered_mixed_energy_sq_le`
- `centeredEnergy_minimizes`
- `mixed_centeredEnergy_le`
- `bad_residue_mass_le`
- `indicator_bad_residue_mass_le`
- `sparse_self_error_floor`
- `chebyshev_certificate_floor`

## Remaining gap

This route has not supplied a compatible scale-changing construction. It
would need stronger structural control on mixed convolutions than their
centered second moments, or a repair method applicable to much denser errors.
Neither has been proved.
