# Direct Padé derivative-specialization congruence

Verified auxiliary arithmetic, NOT a proof or disproof of Erdős 68.
Submission/Spec.lean is unchanged with its original sorry. No settlement has
been obtained or submitted.

DirectPadeDerivativeCongruence.lean compiles without warnings and has a built
olean. Its four printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound. There are no proof holes or numerical premises.

## General weighted-prefix theorem

Write c_n=1/(n!-1) in Q, with c_0=c_1=0 by totalized division, and

    S_n=sum_(k<n) c_k.

For L>=2 and n>=L, prefix_decomposition proves

    S_n=S_L-(n-L)+L!*r,
    gcd(L!,den(r))=1.

Indeed each late coefficient satisfies

    c_n=-1+L!*((n!/L!)/(n!-1)),

and every late row denominator n!-1 is coprime to L!.

For finitely many integral weights w_i, indices n_i>=L, and integers D,a,b,
assume

    D*S_L=a,
    L! divides W=sum_i w_i,
    sum_i w_i*S_(n_i)=b.

Then weighted_prefix_congruence proves

    L! divides D*(b+sum_i w_i*n_i).

Only the early prefix is cleared by D. The proof retains the late rational
denominators, proves their coprimality to L!, and applies the earlier exact
integer_multiple_of_coprime_den lemma. It does not reduce arbitrary rationals
modulo L! without checking their denominators.

## Exact Padé specialization

Let F(z)=sum_(n>=2) z^n/(n!-1), Q in Z[z], and P in Q[z]. Suppose

    deg P<N,
    deg Q+L<=N, L>=2,
    coeff_k(QF-P)=0 for every 0<=k<=N,
    P(1)=b is an integer.

Set D_L=den(S_L). Then

    L! divides D_L*(b-Q'(1)).

The theorem is pade_factorial_dvd_numerator_sub_derivative. The existing
specialization result supplies L!|Q(1). The new file also verifies the finite
convolution identity

    sum_(k=0)^N coeff_k(QF)
       =sum_(j=0)^(deg Q) Q_j*S_(N-j+1),

and its equality to P(1) under the jet hypotheses. Thus the specialization
connection is proved, not merely asserted in prose. The derivative arises from

    sum_j Q_j*(N-j+1)=(N+1)*Q(1)-Q'(1).

Only integrality of P(1) is assumed, not integrality of all coefficients of P.

## Common-factor consequence and limitation

If an integer g divides L! and b, and is coprime to D_L, then g divides Q'(1).
This is factorial_common_factor_dvd_derivative. Since L! already divides
Q(1), such g is a common factor of the specialized pair.

The theorem imposes a constraint on that common factor; it does NOT bound it.
No useful bound on Q'(1), no small-error family after primitive normalization,
and no nonvanishing theorem for the target is supplied. Nothing here asserts
convergence or divergence of Padé approximants in any p-adic field, or identifies
real and p-adic boundary values.

This completes the derivative-congruence idea left informal in the preceding
continuation, but does not close the irrationality argument.

No numerical experiment was run. The compilation log is
/tmp/direct_pade_derivative_congruence.log. All checks have completed; no process
is pending. No complete proof or disproof of the original conjecture is waiting
to be formalized.
