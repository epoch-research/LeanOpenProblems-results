# Rational polynomial kernels: boundary integrality suffices

This is auxiliary progress, not a proof or disproof of Erdős 68.
`Submission/RationalKernelForms.lean` compiles and its printed principal
axiom audits contain only propext, Classical.choice, and Quot.sound.
`Submission/Spec.lean` remains unchanged with its original sorry.

## General rational-coefficient identity

For A in Q and polynomials H_j in Q[X], j=1,...,J, put

    q_j(n)=n^j H_j(n-1)-H_j(n),
    P(n,t)=A-(1-t) sum_(j=1)^J q_j(n)t^(j-1),
    B=sum_(j=1)^J H_j(1).

The verified `hasSum_kernel` gives exactly

    sum_(n>=2) P(n,1/n!)/(n!-1)=A*alpha-B.

The theorem `hasSum_integral_boundary` specializes this to integer A and B.
No integrality or integer-valuedness of the other polynomial coefficients
or evaluations is necessary. Thus clearing every polynomial coefficient is
an unnecessarily strong arithmetic requirement for using the resulting
linear form. Only A and B need to be cleared jointly.

## Exact row zeros do not force divisibility in this larger class

The earlier divisibility lemma applies to integer row coefficients. It must
not be applied to unrestricted rational polynomial kernels.

The verified `cancellation_without_divisibility` uses

    A=1, J=1, H(X)=(-X^2-7X+18)/10.

Here H(1)=1, and the two rows n=2 and n=3 both vanish. Nevertheless 5 does
not divide A. `example_sum` proves that the total form is alpha-1, not zero
and not an error tending to zero.

More generally, `finite_rows_zero_arbitrary_rationals` proves that for ANY
rational A,B and any N, there is H in Q[X] with H(1)=B and with the first N
rows zero. Unlike the earlier integer-valued interpolation theorem, there
is no divisibility hypothesis. The proof uses rational Lagrange interpolation
of the forced node values

    h_1=B,
    h_(n+1)=(n+1)h_n - A*(n+1)!/((n+1)!-1).

The sum remains A*alpha-B regardless of the number of these zeros, so the
finite cancellation condition alone gives neither a size nor a sign bound.

## A lower bound surviving the relaxation

The verified `square_kernel_lower_bound` assumes A>=0 and an identity at
every factorial node of the form

    P(n,1/n!)=A/(n!)^J + (1-1/n!)*r_n^2.

The r_n can be arbitrary real numbers; no rationality or height assumption
is used. Every row is nonnegative, and the n=2 row alone gives

    A/2^J <= A*alpha-B.

In particular, increasing the degrees of H_j at a fixed J cannot give a
sequence of these positive forms tending to zero if A is a positive integer.
One must vary J and control the boundary A,B and total error simultaneously.
No such family has been constructed here, and there is no settlement of
the original conjecture.
