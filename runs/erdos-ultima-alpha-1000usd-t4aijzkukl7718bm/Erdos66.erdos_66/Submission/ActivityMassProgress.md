# Activity-sensitive carry aggregation

## Original conjecture status

Erdos66.erdos_66 is still neither proved nor disproved. Spec.lean is unchanged
and contains its original sorry. Nothing in this branch supplies an infinite
Boolean construction or a universal contradiction.

## Finite aggregation

For nonnegative masses f_i on a finite set S,

    sum_i [30+50 log(f_i+1)]
      <= 30 |S|+100 sqrt(|S| sum_i f_i).

This follows from log(1+x)<=2 sqrt(x) and Cauchy--Schwarz. Write the right
side as budget(K,P)=30K+100 sqrt(KP).

For row families C,D, an old pair (a,z-a) is active at k when

    k<=q, a in C_k, z-a in D_(q-k).

activeSupport contains precisely the old endpoints with nonempty activity.
It is contained in the old half-row support for antitone families, but
empty activity intervals are no longer charged any error. Its sum of
activity lengths is exactly the total mixed coarse mass.

## Actual lower and upper carries

With M>0, b=floor(M sqrt(2)) mod M, t<M, (q+1)^2<=M and antitone C,D,
put rho=(t+1)/M and

    P=sum_(k<=q) r_(C_k,D_(q-k))(t-bq),
    K=number of active old pairs at this target.

The lower-carry count of the phased rows b*k+C_k differs from rho P by
at most budget(K,rho P). The upper-carry error about (1-rho)P is the same,
since lower+upper is the complete count.

For a self-family and q>0, the genuine ordinary count at qM+t therefore
satisfies

    |r(qM+t)-rho P_q-(1-rho)P_(q-1)|
      <= budget(K_q,P_q)+budget(K_(q-1),P_(q-1)).

Both different coarse indices and fine targets are retained. The final
version weakens rho P to P using rho<=1. It does not identify a complete
cyclic count with an ordinary count.

## Asymptotic criterion

For K,P>=0 and L>0,

    budget(K,P)/L=30(K/L)+100 sqrt((K/L)(P/L)).

Consequently K/L->0 and P/L tending to a finite value imply a zero normalized
budget. A bounded normalized mass P<=C L, C>=0, is sufficient; convergence
of P/L is not needed. A two-budget transfer theorem gives convergence of
an actual count from convergence of its proposed mean, with every mass,
support, and error hypothesis stated explicitly. The bounded-mass two-budget variant
requires no limit for either normalized coarse mass.

For L=log n the intended sufficient input is

    K=o(log n), P=O(log n).

No row family satisfying this input compatibly across changing moduli has
been constructed by these lemmas.

## Necessary scope restriction for this certificate

Without any antitonicity assumption, the exact finite mass satisfies

    K <= P <= (q+1)K.

Every active pair contributes at least once and at most q+1 times.
Also budget(K,P)>=30K. Hence, when K>=0, L>0 and P<=C L eventually,

    budget(K,P)/L -> 0  iff  K/L -> 0.

More generally, if P/L->c>0, K/L->0 and P<=(q+1)K, then q->infinity.
No monotonicity of q is required. Thus the new certificate cannot yield
vanishing error at bounded coarse quotients with positive normalized mass.
In particular it does not automatically handle the first few rows after
repeated changes of scale.

This is a statement about the displayed upper-bound certificate, NOT a
lower bound on actual carry discrepancies. Better cancellation or a
different model is not excluded. No extra hypothesis used here is part of
the original existential conjecture.

## Files and verification

Production files, all compiled without warnings with current oleans:

* FiniteLogMassBudgetExplore.lean
* ActivityMassCarryExplore.lean
* ActivityNaturalCarryExplore.lean
* ActivityBudgetLimitExplore.lean
* ActivitySupportScaleExplore.lean

ActivityMassAudit.lean audits all 28 lemmas/theorems. Its saved log reports
only propext, Classical.choice, Quot.sound. No production source contains
sorry, admit, or a new axiom. ActivityScaleChecks.lean is an API-search
scratch file and has intentionally unsuccessful checks; it is not imported
by production files.

The coefficient and all tolerance thresholds must still precede the final
cutoff in the main compactness criterion. This branch does not establish
that finite feasibility, uniform sublogarithmic quadratic rounding, a sharp
repair base, or a universal logarithmic-order fluctuation contradiction.
No valid main submission is ready.
