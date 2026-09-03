# A positive Gram-kernel certificate with integral boundary

This is auxiliary progress, not a settlement. The conjecture in Spec.lean
is unchanged and still contains its original sorry. No proof or disproof
has been submitted.

`PositiveKernelGramExample.lean` is verified. Its principal axiom audits
list only propext, Classical.choice, and Quot.sound.

## Exact verified example

Let

    c(x)=-x^4+9x^3-21x^2-7x+30,
    w(x)=x^4-14x^3+65x^2-116x+65.

The file gives explicit rational polynomials H_1,H_2 of degrees 7 and 2,
with H_3=0 and boundary H_1(1)+H_2(1)=1. For A=1 and J=3, it proves

    P(n,t) = [66560*t^3
               +(1-t)*(65*(c(n+2)+32*t)^2+24*w(n+2)^2)
               +24]/66584.

Thus P(n,t)>0 for every 0<=t<=1. In particular all factorial-node rows are
strictly positive, and their sum is exactly alpha-1. Only A and the total
boundary are integral; the polynomial coefficients need not be cleared.

The example bypasses the previous single-square mod-four obstruction by
using more than one positive square term. It does not contradict that
obstruction.

## How the example was obtained (external development)

The scripts `/tmp/gram_kernel_probe.sage` and `/tmp/gram_kernel_simple.sage`
use exact rational arithmetic. For J=3, write the square polynomial as

    (c_0(n)+t)^2 + tau*w_0(n)^2.

Taking H_2=(n^2-7n+14)/16 forces

    c_0(n)=(1-[n^2 H_2(n-1)-H_2(n)])/2 = c(n)/32.

The degree-four Charlier reproducing polynomial is w_0=w/24. Bell moments
show that tau=27/130 makes 1-c_0^2-tau*w_0^2 lie in the first column
operator's image. The resulting rational boundary is 8323/8320>1.
Mixing this kernel with the constant kernel 1 in proportions 8320/8323
and 3/8323 makes the aggregate boundary exactly one. The Lean file checks
the resulting polynomial identity directly; it does not trust the Sage
calculation or need a formalization of the optimization procedure.

## The unresolved step

This is a finite feasibility certificate, not a sequence of forms tending
to zero. Its sum alpha-1 is fixed, and its implied lower bound for alpha is
weaker than bounds already verified earlier. It is compatible with alpha
being any suitable rational number greater than one.

To prove irrationality one still needs integral A_N,B_N with strict
nonvanishing and |A_N*alpha-B_N| tending to zero. A general Gram-matrix
construction, degree/height bound, or small-error family has not been
obtained. No successful process is running and no complete informal proof
is waiting to be formalized.
