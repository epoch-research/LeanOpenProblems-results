# Fixed-support mass budget for the universal natural operator

## Status

The conjecture remains unresolved. Spec.lean is unchanged with its original
sorry; no valid proof or disproof has been submitted.

## Verified files

* ResidueSupportMassExplore.lean
* DisjointOperatorSupportExplore.lean

Both compile and have current oleans. FixedSupportMassAudit.lean audits all
12 new lemmas/theorems; its saved log contains only the permitted axioms.

## General quantitative support theorem

For a hypothetical witness A, any fixed nonzero modulus M, and any finite
residue set S, define A_S={a in A : a mod M in S}. Exact fiberwise counting
and the existing ordinary residue equidistribution imply

    count(A_S,N)/count(A,N) -> |S|/M.

If B is a subset of A supported on S, then for every epsilon>0,

    eventually count(B,N)/count(A,N) < |S|/M+epsilon.

If A=B union D and B is supported on S, the union cardinality inequality gives

    eventually count(D,N)/count(A,N) > 1-|S|/M-epsilon.

In particular no proper fixed support can be repaired by additions having
zero relative counting mass. This does not assume any structure of the
high-block choices. Nor does it exclude corrections of positive mass.

## Application to the actual natural-number operator

For every K, palette P, and infinite coarse family B,

    a in naturalOperator(M,K,P,B)
      implies a mod M in union_i P_i.

The proof uses the exact membership theorem and map_natCast for reduceDigit;
it does not discard a carry term. Thus no choice of B or K can give the
conjectured limit when this union is proper. The same quantitative repair
mass bound applies to additions to the operator.

For disjoint P_i satisfying the entrywise mixed-count bound

    |r_(P_i,P_j)(z)-mu| <= eta*mu,

the support S=union_i P_i obeys

    |S|^2 <= M*(1+eta)*mu*q^2.

Consequently (1+eta)*mu*q^2<M guarantees that S is proper. Also the old
logarithmically tuned palette theorem can be strengthened: for fixed
c,tau,eta,rho>0 and fixed q, arbitrarily large odd M admit such a palette
with |mu/log M-c|<tau AND |S|/M<rho. This follows from log M/M -> 0,
not a claimed growing-q uniform threshold.

## Consequence and limits

These logarithmic sparse palettes may require a repair carrying arbitrarily
close to all of the eventual witness's counting mass. They cannot be used
as a permanent fine support and then corrected negligibly.

This is not a universal impossibility result. A changing-palette construction
can retain only a finite old prefix, whose eventual mass is negligible; it
is not required to contain an entire infinite fixed-support operator. The
new theorem does not estimate mixed counts across such a change and does not
supply the missing compatible transition, Boolean rounding, or compactness
feasibility theorem.
