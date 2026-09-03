# Prime-field and cyclic finite constructions

## Status of the requested task

**Erdős 66 remains neither proved nor disproved. `Spec.lean` is unchanged and
still has its original `sorry`. No proof submission has been made.**

The results below are finite analogues. They must not be mistaken for the
compatible integer prefixes required by `conjecture_iff_finite_prefixes`.

## Completed finite construction

1. `CarryAveragingExplore.lean`: integer triangular kernel, exact pair count,
   step error at most one, and the abstract two-fiber error estimate.
2. `CyclicThickeningExplore.lean`: an actual cyclic realization. For
   `B ⊆ (ZMod p)^2` with all counts within `E` of `μ`, thicken both coordinates
   by `K` and encode in `ZMod ((p*K)^2)`. The resulting set has all counts
   within `K² E + 2K(μ+E)` of `K² μ`. This needs positive `p,K`, not primality.
3. `SignEnergyExplore.lean`: a greedy sign polynomial of every length `h`.
   Its coefficients are ±1 below `h`, vanish thereafter, and
   `sum coeff(P²)^2 ≤ 2h²-h`, hence `(sum |coeff(P²)|)^2 ≤ 4h³`.
   Proof: append either +X^h or -X^h. The sum of the two new energies is
   exactly `2*old_energy + 8h + 2`, so one sign preserves the bound.
4. `PrimeSignExplore.lean`: CRT plus Dirichlet plus quadratic reciprocity
   realize arbitrary signs at finitely many odd primes, with the new prime
   arbitrarily large and congruent to 1 modulo 8.
5. `IntervalSquareclassExplore.lean`: a positive interval `a,...,a+h-1`
   whose entries each have a private prime factor of valuation exactly 1.
   Choose distinct primes `q_i>h+2`, and impose `a+i ≡ q_i (mod q_i²)`.
6. `IntervalSignExplore.lean`: combines 4 and 5. The interval is chosen
   before the sign pattern; every pattern is realized by infinitely many
   arbitrarily large primes. Factorization and reciprocity handle all factors,
   with the factor 2 harmless because the prime is 1 modulo 8.
7. `PrimeIntervalExplore.lean`: combines 3 and 6 with the parabola identity.
   `exists_prime_parameters` supplies `U ⊆ ZMod p`, `|U|=h`, excluding zero
   and opposite pairs, with `sum |charFiber U| ≤ E`, `E²≤4h³`.
   Polynomial coefficient pushforward can only decrease the l1 norm, so no
   delicate wrapped/unwrapped fiber split is needed for this step.
8. `ParabolaRepairExplore.lean`: a simpler origin repair than the previously
   proposed horizontal powers-of-five set. Choose an unused parameter `w`
   with `w,-w∉U` and `w≠0`. Take a partial parabola of `m` nonzero points
   on `y=x²/w`, and add its negative. These two pieces are disjoint, symmetric
   in union, and disjoint from the original graph set. The origin receives
   exactly `2m` new representations. Every nonzero target receives at most
   `8|U|+8` new representations: mixed curve counts and self-curve counts
   are each at most 2 per parameter pair, including opposite parameters.
   `exists_parabola_origin_repair` needs only enough room in the field.
9. `PrimeFlatExplore.lean`: complete finite combination:
   - `exists_flat_prime_plane`: for `h=2k+1`, arbitrarily large primes `p`
     admit `B ⊆ (ZMod p)^2` with all counts within `E+10h+8` of `h²`,
     where `E≥0` and `E²≤4h³`.
   - `exists_flat_cyclic`: for any positive `K`, an actual cyclic set in
     `ZMod ((p*K)^2)` has all counts within
       `K²(E+10h+8) + 2K(h²+E+10h+8)`
     of `K² h²`.

Principal theorem axiom checks are in `CheckCarryAveraging.lean`,
`CheckSignEnergy.lean`, `CheckPrimeSign.lean`, `CheckPrimeInterval.lean`,
`CheckPrimeFlat.lean`. They use only the three allowed axioms.

## Remaining mathematics

The finite relative error tends to zero as `h,K→∞`:
`E/h² + 10/h + 8/h² + (2/K)*(1+E/h²+10/h+8/h²)`.
Since the prime can be arbitrarily large after fixing `h`, one can tune
`K ≈ sqrt(log p)/h` to make the mean asymptotic to half the logarithm of the
cyclic group size. That parameter-tuning asymptotic is not yet formalized.

Even a fully formal finite logarithmic analogue would NOT settle the integer
conjecture. No construction controls the necessary inhomogeneous truncation
profile at all integer scales with a single threshold function. Actual prefixes
of a witness cannot be uniformly cyclic-flat (`CyclicPrefixExplore.lean`).

Periodic-block gluing still has uncontrolled transition cross-counts between
different finite patterns. Sparse-prefix modifications become harmless far
above their support, but this leaves a gap near each transition. Independent
random interpolation has the familiar fixed-coefficient logarithmic tail
obstruction and has not supplied shrinking relative error uniformly.
