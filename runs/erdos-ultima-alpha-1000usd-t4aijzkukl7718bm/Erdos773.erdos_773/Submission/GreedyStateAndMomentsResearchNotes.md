# Exact greedy states and stopped-process configuration bounds

This does NOT settle Erdős 773. Spec.lean remains unchanged and admitted for
0<epsilon<=1/3. No actual Sidon exponent or endpoint improved in this pass.

## Three new clean modules

1. GreedyHypergraphState.lean (477 lines)
2. StoppedGreedyMoments.lean (357 lines)
3. GreedyConfigurationTails.lean (124 lines)

All are built, admission-free, and warning-free. Their 23 printed audits use
only propext, Classical.choice, and Quot.sound. None imports Spec.lean.
Combined log: /tmp/greedy-state-moment-tail-audit.log.

## Exact states, including multiplicities

For a finite hypergraph H and selected set I:

* Independent H I means no original edge lies wholly in I.
* available H I contains v outside I for which insert v I is independent.
* active H I j indexes ORIGINAL edges e with |e\\I|=j and e\\I contained in
  the available set. Different original edges with the same residual are NOT
  silently merged.
* incident H I j v filters those original edges whose residual contains v.
* closes H I v is the set of available w!=v for which some original edge
  has residual exactly {v,w}.

For any available v, the checked update is

    available(I+v) = available(I) \\ ({v} union closes(I,v)).

Consequently Q(I+v)+1+|closes(I,v)|=Q(I), exactly.

For an independent I in an r-uniform H, every active residual size lies
between 2 and r. In particular, sizes two and three cannot be omitted in a
four-uniform process.

Let r(v,w) count original edges contracted to {v,w}, with v!=w. Then

    d2(v) = sum_{w in closes(v)} r(v,w),
    |closes(v)| <= d2(v) <= K |closes(v)|

when original pair codegrees are at most K. Define

    excess(v) = sum_{w in closes(v)} (r(v,w)-1).

The exact identity is d2(v)=|closes(v)|+excess(v). Also

    sum_{v available} dj(v) = j |active_j|.

Thus the exact finite average after a uniform available choice is

    average Q(I+v)
      = Q-1-(2 |active_2| - sum_v excess(v))/Q,       Q>0.

The correction is necessary; a pair-codegree bound greater than one does
not make the residual two-graph simple.

The module also proves an exact update of every active-edge count. An old
j-edge survives if its entire residual stays available. An old (j+1)-edge
is promoted if it contains the selected vertex and all its other residual
vertices survive. These two families are disjoint, and

    |active_j(I+v)| + |lost_j| = |active_j(I)| + |promoted_j|.

The lost term includes deletion caused by NEWLY CLOSED vertices.

## Stopped greedy averages

Fix L. At a state with at least L available vertices and a nonempty available
set, step averages uniformly over all available choices. Otherwise it holds
the state fixed. The expectation functional is defined recursively by these
finite REAL averages, starting at the empty selected set. No measure-theory
or independent-choice assumption is needed.

Positivity, normalization, linearity, and monotonicity are proved. The main
inclusion bound, valid for L>0 and every prescribed vertex set S, is

    E_t[1_{S subset I}] <= (t/L)^|S|.

The proof bounds the one-step increase by

    (1/L) sum_{v in S} 1_{S\\{v} subset I},

then inducts, using an elementary binomial tangent inequality. The choices
are adaptive and need not be independent. The process may have stopped early.

`configuration_bound` sums these bounds over a family of supports.
`weighted_configuration_bound` allows an arbitrary finite index set, repeated
supports, and nonnegative real weights; repeated supports are counted with
their multiplicities.

An inductive `Reach` relation records actual choices and absorbing holds.
Every reachable state is independent if H has no empty edge, has cardinality
at most t, and, for L>0, satisfies

    |I|=t OR Q(I)<L.

The second alternative is deliberately retained. `expectation_attained_below`
extracts an actual reachable state with test-function value no greater than
its finite expectation. `configuration_free_run` combines this with total
configuration cost <1, but DOES NOT discard the early-stopping alternative.

## Witness and configuration tails

`witness_bound` proves a finite union bound: if each bad event has a fully
selected witness among indexed supports C_i, its expectation is at most
sum_i (t/L)^|C_i|.

For t<=L, if every k-subfamily of a configuration family T has union size at
least m, `configuration_tail` gives

    E_t[1_{at least k configurations selected}]
      <= choose(|T|,k) (t/L)^m.

For pairwise disjoint supports, each of size at least r, the exponent is r*k.
No independence of the configuration inclusion events is assumed.

`simultaneous_good_run` sums finitely many event bounds whose total is less
than one and produces an actual reachable state avoiding them all. It still
returns the alternative |I|=t OR Q(I)<L.

## What remains missing

There is NO proof that the process keeps at least L available vertices up to
a logarithmically enhanced target time. The inclusion and tail bounds alone
do not provide this: they were proved for a process that is allowed to stop.
The exact drift identity is not an asymptotic drift estimate unless residual
degrees and multiplicity errors are quantitatively controlled along the run.

A contemplated random-greedy analysis would track, with V original vertices,
p=t/V, and regular degree D, profiles such as

    q=exp(-D*p^3),
    d2 approximately 3*D*p^2*q,
    d3 approximately 3*D*p*q^2,
    d4 approximately D*q^3.

These are research targets, NOT proved assertions in these modules. A stopping
and concentration argument, including common-neighbor/error configurations,
still has to be proved. No unverified random-greedy theorem is assumed.

Even a verified logarithmic-gain bound would remain at the 2/3 exponent scale.
Obtaining epsilon=1/3 would additionally require adequate constants. It would
not by itself settle any fixed epsilon<1/3. The strongest actual completed
lower bound remains (5/4) N/(N log N)^(1/3).

Main check: /tmp/spec-greedy-state-moments-check.log.
Spec.lean SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
No proof submission was made.

## Subsequent update

GreedyConfigurationTails now additionally exports `markov_bound`; its printed
audit count is six, and the three-module count is 24 rather than 23. Further
all-prefix duplicate and common-neighbor controls, including a simultaneous
reachable-state certificate, are documented in
GreedyOverlapAndPackingResearchNotes.md. Early stopping remains possible.
