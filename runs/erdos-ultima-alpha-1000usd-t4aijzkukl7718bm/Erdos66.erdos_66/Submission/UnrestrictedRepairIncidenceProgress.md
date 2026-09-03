# Unrestricted-sharing repair incidence concentration

## Status and verification

The original conjecture remains unresolved, and `Spec.lean` is unchanged.
`UnrestrictedRepairIncidenceExplore.lean` compiles. The nine principal
results in `UnrestrictedRepairIncidenceAudit.lean` use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact finite accounting

Define

    targetDegree(B,T,x) = #{b in B : x+b in T}.

For disjoint finite A,F, put B=A union F. The exact identity is

    sum_(n in T) (r_B(n)-r_A(n)) + sum_(n in T) r_F(n)
      = 2 sum_(x in F) targetDegree(B,T,x).

Thus a uniform gain d on T requires

    d |T| <= 2 sum_(x in F) targetDegree(B,T,x).

If all new-point degrees are at most H, this becomes d|T|<=2H|F|.
No packet decomposition, independence, Sidon condition, or bound on point
reuse is assumed. New/new representations are explicitly included.

For positive L,R and nonempty T, gains of at least delta L together with

    R targetDegree(B,T,x) <= H |T| L       for every x in F

force delta R<=2H|F|. Hence a sequence with |F|/R->0 and fixed delta>0
cannot maintain these hypotheses on nonempty target sets indefinitely.

## Infinite monotone completions

Suppose A subset B and both counting functions divided by R(N) have the
same limit. Then the old checked difference-count lemma gives
count(B\A,N)/R(N)->0. Applying the finite result to exact cutoffs gives:

If T_N subset [0,N) is nonempty infinitely often, L(N),R(N)>0 eventually,
and r_B(n)-r_A(n)>=delta L(N) at every n in T_N, then for EVERY fixed H
there are arbitrarily large N and a new point x<N in B\A such that

    R(N) targetDegree(cutoff(B,N),T_N,x) > H |T_N| L(N).

There is also an eventual-empty-target formulation when the degree bound
is given as a hypothesis.

## Logarithmic specialization

For a hypothetical completion B with nonzero coefficient c, assume the
base A already has the necessary count asymptotic

    count(A,N)/sqrt(N log N) -> 2 sqrt(c/pi).

The checked Tauberian theorem supplies the same limit for B. With
R(N)=sqrt(N log N), L(N)=log N, persistent delta log N deficits require
new points whose target degrees exceed

    H |T_N| sqrt(log N)/sqrt(N)

for every fixed H along arbitrarily large scales. This is an explicit
necessary concentration property for unrestricted shared-point repairs.

## Scope

The target-degree bound is NOT established for the actual exceptional sets
of the probabilistic base, nor for all conceivable completions. The theorem
does not bound these degrees universally and does not show that the required
concentrations are impossible. It is not a disproof of the original
existential statement and constructs no completion.

The reference URL was also checked during this continuation, but external
DNS resolution was unavailable. No claim about a new external result was
obtained.
