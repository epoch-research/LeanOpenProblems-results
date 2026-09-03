# Positive kernels and the finite-column ceiling

This is auxiliary progress, NOT a settlement of Erdős 68. Spec.lean is
unchanged and retains the original sorry. No proof or disproof was submitted.

## Verified exact identity

`Submission/PositiveKernelColumnBound.lean` compiles and has a built olean.
Its three printed axiom audits use only propext, Classical.choice, and
Quot.sound.

Write

    beta_J=sum_(j=1)^J E_j,  E_j=sum_(n>=2) 1/(n!)^j,
    R_J=sum_(n>=2) 1/[(n!)^J*(n!-1)],
    alpha=beta_J+R_J.

Suppose the existing rational-polynomial kernel satisfies, at every factorial
node t_n=1/n!,

    P(n,t_n)=A*t_n^J+(1-t_n)*S_n.

The new theorem `hasSum_residual` proves the exact identity

    sum_(n>=2) S_n/n! = A*beta_J-B,

including summability. No sign assumption is needed for this identity, and
only A and the aggregate boundary B are relevant to arithmetic clearing.

If S_n>=0, then `boundary_le_truncated` and
`full_remainder_lower_bound` give

    B<=A*beta_J,
    A*R_J<=A*alpha-B.

This includes square kernels and finite positive-semidefinite Gram kernels.
It strengthens the earlier row-two estimate by retaining the entire omitted
column tail. At fixed J, increasing polynomial degree alone cannot remove
this baseline. It does NOT exclude a suitable family with varying J.

## Exploratory SDP formulation (not a proof certificate)

The external script `/tmp/gram_kernel_sdp.py` sets

    S(n,t)=v(n,t)^T G v(n,t), G positive semidefinite,

where v uses Poisson-orthogonal Charlier polynomials through degree D in n
and powers of t through (J-1)/2, for odd J. The coefficients of
1-S(n,t) must belong columnwise to the images of

    H(n) -> n^j H(n-1)-H(n).

Polynomial reduction computes these linear constraints exactly before
converting their matrices to floating point. With A=1 the objective is the
endpoint expression B=S(0,1)+S(1,1)-2J. A basic ADMM iteration alternates
projection onto the affine constraint space and the PSD cone. This was a
structured construction test, not a search for a counterexample to alpha.

Three runs of 20000 iterations produced the following DIAGNOSTIC objectives:

    D J | objective B           | beta_J (diagnostic)
    4 3 | 1.1275694869767694    | 1.1275696797784189209...
    4 5 | 1.2222223953718299    | 1.2222230300747136007...
    6 7 | 1.2456855461263672    | 1.2456855412414568545...

The last displayed objective is slightly ABOVE the proven ceiling. This is
numerical residual error, not a counterexample: its matrix is not an exact
feasible PSD certificate. No floating-point output was imported into Lean,
and no exact positivity certificate is claimed for these matrices.

The outputs suggest that the finite-degree construction can closely
approximate the finite-column ceiling. They establish neither exact optimality
nor asymptotic convergence, and do not control any reduced boundary denominator.
The saved matrices are `/tmp/gram_sdp_D4_J3.npz`,
`/tmp/gram_sdp_D4_J5.npz`, and `/tmp/gram_sdp_D6_J7.npz`.
No optimization process remains running.

## Remaining construction problem

Even an exact positive rational Gram certificate near beta_J would only give
one lower rational approximation. For irrationality one still needs integers
A_J,B_J with positive errors tending to zero against the FULL alpha. The
baseline alone requires A_J*R_J -> 0, and hence A_J/2^J -> 0. No uniform height
bound meeting this condition together with a small non-baseline residual has
been obtained. Numerical closeness at fixed J supplies no such bound.

There is no complete informal proof awaiting formalization. The original
conjecture is still unproved and undisproved in this work.

## Later verified escape from this specific ansatz

PhysicalPositiveKernelExample.lean now supplies an exact positive quadratic
kernel with A=4,B=5,J=2 and 0<4*alpha-5<1. Its positivity uses a Gram block
weighted by x-2, and is required only for x>=2. The theorem no_column_baseline
verifies that it cannot have the A*t^J+(1-t)*nonnegative-residual form assumed
above. Thus it does not contradict this file's lower bound. See
PhysicalPositiveKernelsNotes.md. No growing small-form family is established.
