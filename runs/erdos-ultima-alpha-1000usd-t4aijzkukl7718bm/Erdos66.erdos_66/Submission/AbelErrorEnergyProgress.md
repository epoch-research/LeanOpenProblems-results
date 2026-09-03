# Direct Abel error-energy lower bound

## Original task status

The original conjecture is unresolved. `Submission/Spec.lean` remains
unchanged with its original `sorry`. No proof or disproof has been submitted.

## New checked theorem

For any hypothetical witness A,c, write e(n)=r_A(n)-c log n. Then

  liminf_(r -> 1-) [(1-r)/(-log(1-r))] * sum_n e(n)^2 r^n >= c.

The formal statement uses the equivalent eventual form: for every real
d<c, the normalized energy is eventually strictly greater than d.
There is NO additional assumption that e(n)^2/log n converges, nor any
assumed pointwise envelope for e(n)^2.

This is more direct than the earlier sharp envelope theorem, which gave
c<=d when a pointwise squared-error envelope asymptotic to d log n was
supplied. It does not improve the fluctuation scale from sqrt(log n) to
log n.

## Proof pipeline

`AbelErrorEnergyExplore.lean`, namespace `Erdos66AbelErrorEnergy`:

* `summable_errorSq`: the harmonic-centered squared-error power series is
  summable at every 0<=r<1, for ANY A and real c. The proof uses the crude
  polynomial bounds r_A(n)<=n+1 and H_(n+1)<=n+1.
* `root_tendsto_one_left`, `eventually_of_eventually_power`: transfer an
  eventual assertion along r^m back to all radii, using the positive real
  m-th root.
* `tilted_gap_limit`: the existing tilted squared-mass gap, normalized by
  the kernel, tends to c/(2k+2).
* `normalized_error_energy_eventually_gt`: multiply by the power-kernel
  ratio, obtaining c(2k+1)/(2k+2), then take k large enough for any d<c.
* `perturbed_center_energy_eventually_gt`: any replacement center g with
  (g(n)-c H_(n+1))^2=o(log n) retains the same lower coefficient. Young's
  inequality bounds the energy change; the center-error Abel energy tends
  to zero.
* `logarithmic_error_energy_eventually_gt`: apply the preceding result to
  g(n)=c log n, using convergence of H_(n+1)-log n.

The development file compiles with a built olean.
`AbelErrorEnergyAxiomCheck.lean` audits the main results; only propext,
Classical.choice, and Quot.sound occur.

## Reviews in this pass

Fixed arithmetic progressions and additional geometric tilts were checked
for a possible amplification. No improved logarithmic-order fluctuation
bound was obtained. The lower energy scale is N log N, while the original
conjecture permits squared-error mass o(N log^2 N); these remain compatible.

The nearby-period padding formulas were also reviewed. They give the same
natural realization when the source template and repetition count are
fixed, but not compatibility when the source prime or density family
changes. Long complete repetition still has the already checked progression
peak restriction. No new scale-changing mixed-count theorem follows from
padding alone.

## Remaining gap

A resolution still requires either a compatible infinite construction with
pointwise o(log n) error, or a universal obstruction on a larger scale than
the squared-error logarithmic lower bound above. Neither has been proved.
