# Sparse perturbations separate the moving-window result from pointwise control

## Original task status

The conjecture in `Submission/Spec.lean` is still unproved and undisproved.
Its statement and original `sorry` have not been changed. No final proof
has been submitted. The results here do NOT negate its existential claim.

## A checked concrete separation

Write A for the canonical floor-rounded fractional profile, and put

    D = union over k>=0 of [(k+1)^8, (k+1)^8+k+1),
    B = A union D.

The SAME explicit set B satisfies both:

1. For every width function w with eventually 0<w(n)<=n and

       n / (w(n)^2 log n) -> 0,

   the moving representation average on (n,n+w(n)] divided by
   w(n)*log(n) tends to 1.

2. At the targets

       t(k) = 2*(k+1)^8+k,

   the normalized pointwise counts r_B(t(k))/log(t(k)) tend to infinity.
   In particular, B has no finite pointwise normalized limit.

This shows that even the FULL moving-window theorem previously established
for A cannot by itself imply a pointwise bound or a pointwise limit. It
does not decide whether the unperturbed rounded set A is a witness, and
does not rule out other sets.

Main theorem:

    Erdos66SparsePackets.spiky_averaged_example_of_width

The simpler sqrt(n)<=w(n)<=n version, including the no-finite-limit
conclusion, is `spiky_averaged_example`.

## Finite estimate and stability theorem

`Submission/WindowPerturbationExplore.lean`, namespace
`Erdos66WindowPerturbation`, establishes:

* `rounded_local_count_sqrt`: all intervals of length w contain at most
  2+sqrt((2w+1)*H_(2w+1)) points of A. This uses prefix discrepancy and
  antitonicity of the fractional profile.

* `window_union_error_bound`: for ANY natural sets A,D, if each length-w
  interval contains at most L points of A, then, writing M=count_D(n+w+1),

      0 <= sum_(n<k<=n+w) [r_(A union D)(k)-r_A(k)] <= 2*M*L+M^2.

  This follows by counting old-new and new-new ordered pairs. No
  disjointness hypothesis is needed.

* `rounded_union_window_limit_of_width`: if count_D(N)^4<=N for every N,
  adjoining D preserves every width limit covered by the previous rounded
  theorem (including its shorter-than-sqrt(n) widths).

For the last step, the perturbation divided by w*log(n), when squared, is
bounded by

    144*x*(1+log(5)+log(n))/log(n) + 2*x^2,
    x = count_D(n+w+1)^2 / (w*log(n)).

The quartic count bound and w<=n imply

    x^2 <= 3*n/(w^2*log(n)^2) -> 0.

The square here is outside the window sum, not inside it.

## Explicit sparse packets

`Submission/SparsePacketsExplore.lean`, namespace `Erdos66SparsePackets`:

* `sparsePackets_quartic_count`: count_D(N)^4<=N at EVERY cutoff N.
  Take the largest active packet index K. The total packet mass through K
  is at most (K+1)^2, and the last packet starts at (K+1)^8<N.
* `packet_peak`: every superset of D has at least k+1 representations at
  t(k), by reflection within packet k.
* `log_packetCenter_div_index`: log(t(k))/(k+1)->0.
* `packets_peaks_atTop`: every superset of D has the normalized peaks
  tending to infinity along t(k).
* `packets_exclude_finite_limit`: every superset of D has no finite
  pointwise normalized limit.

## Verification

Both production files compile and have current oleans.
`Submission/WindowPerturbationAxiomCheck.lean` audits the principal results;
only `propext`, `Classical.choice`, and `Quot.sound` occur.

The unresolved point remains pointwise quadratic rounding error or another
compatible infinite construction. The checked averaged analogue, even in
its strongest established form, does not supply that property.
