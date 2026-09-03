# Uniform global one-target repair

## Status

The conjecture in `Spec.lean` remains unresolved, and its original `sorry`
is unchanged. This is a constructive auxiliary theorem, not a submitted
solution or disproof.

## New theorem

`Erdos66GlobalRepair.eventually_global_repair` proves the following.
Fix D,K,C>=0 and epsilon>0. For every sufficiently large natural target n,
uniformly over every A subset of the naturals satisfying

    r_A(z) <= K + C log(z+2)       for all z,

and every natural m<=D log n, there is a finite packet F such that:

* F has exactly 2m elements and is disjoint from A;
* n<=4a and a<=n for every a in F;
* r_(A union F)(n)=r_A(n)+2m exactly;
* at every z != n,

    0 <= r_(A union F)(z)-r_A(z) <= epsilon log(z+2).

The starting threshold depends only on D,epsilon,K,C, not on A or m.
All targets z are controlled, including arbitrarily large ones.

## Proof pipeline (all compiled)

1. `UniformSelectionExplore.lean`: uniform finite product averages;
   arbitrary-tilt MGF bounds for hit counts; a simultaneous avoidance/hit
   criterion. A bad event with at most one choice in one coordinate has
   probability at most 1/q.
2. `SidonSelectionExplore.lean`: choose m points with all unordered sums
   distinct, avoiding a forbidden set and satisfying all hit bounds.
   There are at most m^4 Sidon-collision events and m*|B| forbidden events.
3. `SymmetricSidonExplore.lean`: reflect a Sidon set D in n/2. The packet
   D union (n-D) has 2|D| representations of n, at most six of every other
   target, and exactly 2|D| points when D lies strictly below n/2.
4. `FiniteRepairExplore.lean`: combine the preceding facts. Avoiding A
   makes the mixed count at n zero, so the increase there is exact.
   At other tested targets the collateral increase is <4R+6.
5. `LocalWindowExplore.lean`: if all representation counts of a finite set
   are <=V, its intersection with any interval of length L has size
   <=sqrt(2LV). This bounds all forbidden and mixed-hit choice densities.
6. `RepairParametersExplore.lean`: for m<=D log n, L>=n/24, and
   W=B sqrt(n) log n, the selection criterion tends to zero when testing
   n^h+1 targets with R=epsilon log(n)/16 and fixed tilt
   t=32(h+1)/epsilon. The key small quantity is log(n)^2/sqrt(n).
7. `NaturalRepairBridgeExplore.lean`: truncation, integer/natural conversion,
   and the crude global bound that adding F raises any count by <=2|F|.
8. `GlobalRepairExplore.lean`: choose h>=1 with 4D<=epsilon*h and truncate
   A at X=n^h. Test every z<=X. Beyond X the crude bound 4m is already
   <=epsilon log(z+2). Below the packet support nothing changes.

`RepairAxiomCheck.lean` audits the pipeline and final repair theorem.
All checked results depend only on propext, Classical.choice, Quot.sound.

## Remaining obstacle

This does not justify repairing every target in succession. The collateral
errors from many packets may accumulate. The theorem's threshold depends on
epsilon, and there is no proof that a summable error budget can handle all
large deficient targets. In particular, the earlier annulus constructions
leave whole intervals of uncontrolled targets, not a sufficiently sparse
exceptional set.

Possible next use: establish a rigorous iteration for sufficiently sparse
exceptions, or a simultaneous multi-target repair that is much more efficient
than adding one packet per target. Neither has yet been proved.
