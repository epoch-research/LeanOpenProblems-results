# Fixed coefficient outside a summable exceptional set

## Main conjecture status

The original conjecture is still unproved and undisproved. Spec.lean is
unchanged with its original sorry. No proof or disproof has been submitted.

## New positive infinite result

`Erdos66DensityOneLogLimit.exists_log_limit_off_summable_exception`:

For EVERY prescribed c>0 there exist A,E subsets of N with

    sum_{n in E} 1/(n+2) < infinity,
    count(E,N)/N -> 0,
    r_A(n)/log n -> c outside E.

The final condition is stated in Lean as convergence of the function that
replaces the quotient by c at indices in E. E is not asserted to be finite.

The intermediate result
`Erdos66HarmonicExceptionalProfile.exists_harmonically_summable_exceptions`
keeps the same c and the same A for all epsilon>0 and proves summability of

    1_{|r_A(n)/log n-c| >= epsilon}/(n+2).

Unlike the earlier fixed-relative-tolerance theorem, c DOES NOT change as
the tolerance shrinks. The cost is the exceptional set.

## Checked proof

* `BiasedTailPotentialExplore.lean` bounds a two-sided exponential potential
  with target T when the Bernoulli mean m satisfies
  m<=2T and |m-T|<=delta*T/2. Its expectation is at most
  2 exp(-delta^2*T/64). The potential is at least one on the bad event.
* `HarmonicExceptionalProfileExplore.lean` uses the exact fractional profile
  scaled to c and its finite-mean approximation uniform in cutoff. Dividing
  the potential by n+2 gives the summable bound

      2/(n+2)^(1+delta^2*c/128).

  For delta_j=1/(j+1), thresholds are chosen so each tail expectation is at
  most 2^(-j)/4. One finite realization controls the combined costs for all
  j and n below any final cutoff.
* `SummableCostCompactnessExplore.lean` passes these fixed continuous cost
  constraints to one Boolean sequence, hence one natural-number set. Every
  row of nonnegative costs is summable.
* `SummableExceptionalSetExplore.lean` diagonalizes the exceptional sets at
  countably many tolerances, with a summable geometric budget, to obtain
  one harmonically summable E outside which convergence holds.
* `DensityOneLogLimitExplore.lean` also proves directly that harmonic
  summability implies natural density zero.

All production files compile and have built oleans. The main results are
audited in `HarmonicExceptionalAxiomCheck.lean` and
`DensityOneLogLimitAxiomCheck.lean`, using only the permitted axioms.

## Remaining mathematical gap

The exceptional indices cannot be discarded in the original conjecture.
Harmonic summability is weaker than the existing repair hypothesis, which
charges actual deficits times sqrt(log(n+2))/sqrt(n+1). Nor has an asymptotic
upper envelope at every target been proved for this selected A. Thus neither
hypothesis required by the existing completion theorem is being asserted.

A repair reusing points across substantially denser exceptional sets, or a
structured construction that avoids them altogether, remains missing.
