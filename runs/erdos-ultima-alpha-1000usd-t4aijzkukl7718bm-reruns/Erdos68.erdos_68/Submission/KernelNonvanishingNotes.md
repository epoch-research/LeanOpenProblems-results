# Automatic nonvanishing of nonnegative polynomial kernels

This is auxiliary progress only. Spec.lean is unchanged and is not settled.

`KernelNonvanishing.lean` proves:

* `natDegree_columnOperator`: the column operator raises the degree of
  every nonzero polynomial by j+1;
* `columnOperator_eq_constant`: the only constant in its image is zero;
* `tendsto_row_mul_recip_pow`: any polynomial column coefficient times a
  positive power of reciprocal factorial tends to zero;
* `tendsto_kernel_remainder`: for J>0, the factorial-node kernel equals
  A-rowCoeff(H_0,1,n)+o(1);
* `polynomial_abs_eventually_ge`: a nonzero real polynomial evaluated at
  n+2 is eventually bounded away from zero;
* `eventually_kernel_ne_zero`: a fixed rational polynomial kernel with
  A!=0 is nonzero at every sufficiently late factorial node;
* `positive_form_of_kernel_nonneg`: if all physical-node rows are
  nonnegative, A*alpha-boundary(H,J)>0, without a separate positive-row
  hypothesis.

The first-column polynomial cannot equal a nonzero constant, by the new
elementary degree lemma. No irrationality theorem is needed for this step.
The higher-column terms go to zero, while the first surviving polynomial is
bounded away from zero. J=0 is handled separately. The file imports only
PositiveKernelBoundary and its existing dependencies.

The file compiles without warnings, has a built olean, and both principal
axiom audits list only propext, Classical.choice and Quot.sound.

This removes a nonvanishing obligation for future positive kernel families.
It does not construct an integral boundary, give a uniform error bound, or
supply a sequence of small integer forms. The main gap is still mathematical.
