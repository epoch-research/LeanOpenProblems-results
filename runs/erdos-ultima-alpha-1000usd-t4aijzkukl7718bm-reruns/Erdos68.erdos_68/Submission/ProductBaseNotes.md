# Product-denominator base (not a solution)

Write d_n=n!-1, S_n=sum_(k=2)^n 1/d_k, alpha=sum_(k>=2) 1/d_k,
D_n=product_(k=2)^n d_k, and R_n=D_n*(alpha-S_n), for n>=2.

Since D_n*S_n is an integer,

    frac(R_n) = frac(D_n*alpha).

The exact recurrence is

    D_(n+1)=d_(n+1)*D_n,
    R_(n+1)=d_(n+1)*R_n-D_n.

Suppose alpha=p/q for integers p and q>0. For n>=q, q divides (n+1)!,
so d_(n+1)=-1 modulo q and D_(n+1)=-D_n modulo q. Hence

    frac(R_(n+2))=frac(R_n)

for all sufficiently large n. More precisely, successive fractional parts
are both zero, or alternate between c and 1-c.

This necessary condition is exact, but no contradiction with it has been
proved. It is not a small-tail argument: R_n is of order D_n/(n+1)!,
which grows rapidly. The recurrence above is the previous cleared-tail
recurrence divided by q, so its integrality alone supplies no new descent.

Conversely, equality frac(D_(n+2)*alpha)=frac(D_n*alpha) even at one index
would imply that (D_(n+2)-D_n)*alpha is an integer. Since the multiplier is
nonzero, that already implies alpha is rational. Thus excluding these
repetitions is another irrationality criterion, not an established result.

These observations are mathematical notes, not new Lean declarations.
No proof or disproof of Erdos 68 was obtained. Spec.lean is unchanged.
