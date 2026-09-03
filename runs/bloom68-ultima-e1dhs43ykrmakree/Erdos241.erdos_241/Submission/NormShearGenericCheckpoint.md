# Norm-shear generic collision checkpoint — unformalized research report

Neither target is proved. No positive selector is known. This note records a research-agent argument for future auditing; its algebraic-geometric counting/descent claims have NOT been independently established by the parent. Do not use it as a verified asymptotic theorem.

Parent check: Sage independently verified the two displayed F1/G polynomial expansions and the derivative at (1,1). This checks those algebraic identities only; it does not certify the local-fiber derivation, geometric-component claims, descent, or an arbitrary-subset density theorem.


Let r=3^e, e odd, q=r^2; F_q=F_r(i), i^2=-1. Let Tr(a)=2, theta^3-theta=a. Put u(t)=a+t^3-t, L(A+iB)=A+i(B+A), and

    phi(t)=(theta+t)/(theta+t+1) * L(u(t))^2.

The q values lie in the square subgroup of order (q^3-1)/2. A cyclic disproof construction would require a strong B3 subset of density rho>2^(-1/3), uniformly on an unbounded subsequence.

## Full collision criterion

For plus-root cubics P(X)=product(X+x_j), Q(X)=product(X+y_j), f=X^3-X-a, and S(P)=product L(u(x_j)), the report gives the exact criterion

    Q-f=lambda(P-f), lambda in F_q*,
    S(P)=epsilon S(Q), epsilon=+1 or -1.

It includes all multiplicities. Splitting the norm-one and scalar factors is justified by gcd(q^2+q+1,q-1)=1. The same argument with quadratics shows the full candidate is B2, so a nontrivial triple collision has no cross-side shared parameter. Restriction of scalars to F_r makes this a bounded-degree system of 8 equations in 14 coordinates, despite the original growing exponent.

## Claimed generic-component argument

At a=2 over F_3, use the archived audited seed h=1+i, lambda=1+i, s=0, t=-1+i, P=(X+t)^3, Q with parameters -h,0,h, epsilon=-1. The report claims:

1. The 8 defining equations have Jacobian rank 8 at the seed. After solving the six pencil differentials, the remaining complex differential is

       delta F=-i L(T)-(1-i)(A+B),
       T=sum delta x_j, delta lambda=A+iB.

   This selects a geometrically irreducible 6-dimensional component defined over F_3.

2. Local quasi-finiteness at the AP side, needed to rule out an exceptional fiber component, follows from explicit equations in h=H+iJ. Put

       P0=H^3-H, Q0=-J^3-J,
       c=1-H^2+J^2, d=HJ,
       U=1+c+d, V=-1-c+d,
       n=H^2+J^2,
       B0=n^2+H^2-J^2+1,
       A0=n^2-H^2+J^2+1,
       m=n B0.

   Two necessary local equations are

       F1=U^3 Q0-V^3 P0=0,
       G=A0(m-A0)^2+n B0^3(H+J)^2=0.

   The reported expansions at H=1+alpha,J=1+beta are dF1/dalpha=-1,

       F1(1,1+beta)=beta^6(1-beta-beta^3),
       G(1,1+beta)=-beta^3+O(beta^4).

   Thus F1 gives alpha=O(beta^6), and G makes the reduced local fiber isolated. This would imply domination and generic finiteness of both triple projections. Removing proper closed subsets would leave six-distinct collisions.

3. Lang–Weil would then count at least q^3/72-O(q^(11/4)) unordered six-distinct collision pairs for odd e with 3 not dividing e, for any a of trace2. The error comes from dimension6 over F_r. Extension e=1 mod6 uses a=2, e=5 mod6 uses a=1 and negation. Other trace2 a are Artin–Schreier translates.

4. For 3 dividing e, descent twists by simultaneous parameter translation tau:t->t+1. Its action on the geometric components is not determined. The archived q=729 repeated/AP counts do not resolve this. A generic-count extension needs tau-invariance or another smooth rational seed with local quasi-finiteness.

The agent also proposed an O(q^3) upper bound from fibers of dimension at most1; that exceptional-fiber argument remains unaudited here.

## Exact unresolved obligations

Even a valid Theta(q^3) generic collision count would NOT exclude a 0.794-density independent subset. One needs an arbitrary-subset incidence theorem or a sufficiently strong vertex-cover bound, not Lang–Weil for the entire parameter space. No such bound was obtained. Conversely no selector hitting every collision with fewer than (1-2^(-1/3))q deletions was constructed.

An integer-only lift rescue requires additional winding analysis: modular collisions are not automatically equalities between selected integer lifts. None of these reports settles the conjecture in Spec.lean.
