# Quantitative repeated-period restriction

The original conjecture is still neither proved nor disproved. `Spec.lean`
is unchanged and contains its original `sorry`.

## Completed result

`RepeatedPeriodBarrierExplore.lean` formalizes a restriction on one proposed
scale-transition method. It uses only `Submission.Explore`.

- An arithmetic progression a,a+d,...,a+d*K contained in A, with d>0,
  gives at least K+1 ordered representations of 2a+d*K.
- If r_A(n)/log(n) tends to c, then eventually, whenever

      N <= a <= 2N,    N <= d*(K+1) <= 2N,

  such a progression must satisfy

      K+1 <= (c+1) log(6N),
      N <= (c+1) log(6N) d.

  Thus a nonempty pattern fully repeated across a macroscopic interval
  cannot have period o(N/log N).
- For two such progressions at a common scale N_k tending to infinity,
  with periods d_k and e_k, the theorem

      Erdos66RepeatedPeriodBarrier.scale_div_period_product_zero

  gives

      N_k / (d_k e_k) --> 0.

  The proof bounds this ratio by
  (c+1)^2 log(6N_k)^2/N_k, which tends to zero.

`RepeatedPeriodBarrierAxiomCheck.lean` audits the principal declarations;
only propext, Classical.choice, and Quot.sound occur.

## Scope and limitations

The last theorem requires that the two repeated patterns both occur as
specified in the putative witness. It does not cover arbitrary varying
colors, arbitrary sparse high-block selection, or changes with no long
complete repetition. It proves no universal contradiction.

It explains why a gluing argument based on averaging over a complete product
of two periods cannot operate at the transition scale for fully repeated
macroscopic templates: the required product period is much larger than that
scale. The existence of a different compatible infinite construction remains
unresolved.
