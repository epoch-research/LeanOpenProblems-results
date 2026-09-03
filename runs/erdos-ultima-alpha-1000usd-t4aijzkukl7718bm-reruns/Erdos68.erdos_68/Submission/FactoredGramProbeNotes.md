# Factoring initial factorial-node zeros into the Gram ansatz

This was an external finite construction test, not a Lean theorem or a
settlement. Spec.lean remains unchanged.

Let Z(t)=product_(k=2)^N(1-k!*t). The tested kernel was

    P(x,t)=Z(t)^2/Z(1)^2 * [t^J+(1-t)*S(x,t)],

with J odd and S a positive-semidefinite polynomial Gram form. It has A=1
and zeros at t=1/k! for every x, a stronger condition than zeros only at the
physical pairs (x,t)=(k,1/k!). The column constraints were obtained by
reducing polynomials modulo H -> x^j H(x-1)-H(x).

The objective was

    B=S(0,1)+S(1,1)-2J-4 Z'(1)/Z(1).

Script: /tmp/factored_gram_kernel_sdp.py. Completed tests used
(D,J,N)=(4,3,2),(6,3,3),(6,3,2),(8,3,2),(6,5,2).
The reported numerical objectives were negative, and some feasibility
residuals were substantial. These are NOT exact positivity certificates,
NOT bounds for the optimal objective, and NOT an impossibility theorem.
No asymptotic conclusion follows. No process remains running.

The subsequent physical-index construction in PhysicalPositiveKernelsNotes.md
is different: it uses a Gram block weighted by x-2, allowing the polynomial
to be negative at x=0 or x=1 while preserving positivity at all physical rows.
That construction yielded the exact Lean-checked A=4,B=5,J=2 certificate.
