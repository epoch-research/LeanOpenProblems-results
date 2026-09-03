# Construction reassessment

## Status

The original conjecture is still neither proved nor disproved.
`Submission/Spec.lean` remains unchanged with its original `sorry`.
No proof has been submitted.

An attempt to retrieve https://www.erdosproblems.com/66 again failed with DNS
resolution error. No external resolution or new literature result was verified.

## Reviewed routes

### Dependent rounding

The exact fractional harmonic profile and the sublogarithmic-prefix extension
remain valid. They remove the mixed term, but do not estimate the quadratic
self-convolution of rounding error. Neither bounded nor sublogarithmic prefix
discrepancy alone supplies the required uniform quadratic estimate.

No new choice of rounding parameters has been proved to satisfy it. Finite
numerical behavior of the existing floor rounding is not used as an asymptotic
proof or disproof.

### Hybrid low/high templates

A possible transition scaffold would keep an old low template B in a group
of order M while putting a new finite-field template in the high coordinate.
At the same low modulus, B and the full group have exactly constant mixed
count |B|. Thus a common high-field family could in principle control mixed
terms while the old low restriction is removed.

There is a substantial parameter issue. If |B|^2/M is beta, replacing B by the
full low group changes the low self-mean from beta to M. To keep the same
total mean, the new high self-mean must shrink by beta/M. Existing all-target
flat high-template results do not furnish an arbitrarily small nonzero mean;
they require a positive mean that grows with the requested precision. As a
result the transition needs log-scale budget large compared with M. No
construction was found that reaches this transition while preserving the
required intermediate profile and one fixed logarithmic coefficient.

Assigning low translations as colors of high points also remains unproved.
Simply duplicating a high template for every color increases density, while
partitioning it requires mixed estimates at much smaller means. Neither is
justified by the existing common-period flat-family theorem.

These observations do not prove that every hybrid construction fails. They
identify unresolved requirements of the specific scaffold reviewed here.

### Repair

The actual-deficit weighted completion theorem still requires both an upper
tail of coefficient c and summability of the remaining weighted deficit.
No reviewed construction supplies these hypotheses. Dense transition gaps
cannot be declared harmless or repaired by invoking the sparse-exception
results.

## Conclusion

No result in this reassessment can replace the original sorry or serve as a
theorem proving the negation of the original existential statement.
