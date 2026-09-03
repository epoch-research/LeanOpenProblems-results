# Actual centered-degree signless gaps can be arbitrarily small

## Status: Erdős 773 remains UNSETTLED

The unchanged Spec.lean still has its sole sorry at line 2031, for
0 < epsilon <= 1/3. The actual strongest completed lower bound remains
M(N) >= N^(2/3)/500 eventually. The coefficient-one endpoint is NOT proved,
and no exponent improvement or disproof was obtained. No proof submitted.

Spec SHA-256:
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14

## What was checked

The sharp collision coefficient by itself still does not justify a sharp
greedy horizon. The existing symmetric-energy program has an unresolved
shrinking-scale problem. One possible attempted shortcut would be to
assert a degree-times-variance lower bound for signless dissipation on
ACTUAL centered degrees, rather than on an arbitrary test vector.
The new modules disprove that universal bound and realize the obstruction
inside a legal linear four-uniform greedy residual state.

### BipartiteDegreeEnergy.lean

For K_(m,n), let c be the actual mean degree, e(u)=degree(u)-c,
E=sum_u e(u)^2, and S=(1/2)sum_uv W(u,v)(e(u)+e(v))^2.
All of the following are proved:

    c = 2mn/(m+n),
    E = mn(m-n)^2/(m+n),
    S = mn(m-n)^4/(m+n)^2.

For m=k and n=k+1:

    E = k(k+1)/(2k+1),
    S = k(k+1)/(2k+1)^2,
    2k(k+1) S = c E.

arbitrarily_small_gap proves, for EVERY delta>0, existence of a positive
integer k with E>0 and S < delta*c*E. This is a parametric theorem, not just
a numerical example. The two vertex degrees differ by only one.

### BipartiteGreedyResidual.lean

For arbitrary finite types alpha,beta, use core vertices alpha+beta and
two private label vertices per pair (a,b). The edge indexed by (a,b) is

    {left(a), right(b), label(a,b,false), label(a,b,true)}.

Take I to be all labels. The file proves:

- every original edge has size four;
- distinct original edges intersect in at most one vertex (linearity);
- I is independent;
- every ordering of the labels is legal: any unchosen label is available
  after any subset of the other labels has been chosen;
- the available set after I is exactly the core;
- the original-edge-indexed residual pair weights are exactly K_(m,n);
- actual two-degrees, their actual mean, variance, and signless dissipation
  equal the quantities in BipartiteDegreeEnergy.

Thus the small gap is not an artifact of using a symmetric matrix unrelated
to residual hypergraphs or of inserting an arbitrary error vector.

## Scope restrictions

- The lifted hypergraph is NOT claimed to be initially regular. Its core
  degrees are m or n and its private labels have degree one.
- It is NOT claimed to be a square-collision hypergraph.
- The result does not exclude a spectral estimate under additional
  hypotheses, a high-probability estimate for a specified process, or an
  alternative algorithm exploiting bipartite structure.
- It does not bound the maximum independent set adversely: a complete
  bipartite graph itself has a large independent side.
- It does not disprove Erdős 773, and cannot fill the sorry in Spec.

## Verification

Both modules build cleanly and have oleans. All 15 printed main audits use
only propext, Classical.choice, Quot.sound. They contain no admissions and
neither imports admitted Spec.lean.

Fresh logs:

    /tmp/bipartite-degree-energy-final.log
    /tmp/bipartite-greedy-residual-final.log

The main file and its sole import remain unchanged.
