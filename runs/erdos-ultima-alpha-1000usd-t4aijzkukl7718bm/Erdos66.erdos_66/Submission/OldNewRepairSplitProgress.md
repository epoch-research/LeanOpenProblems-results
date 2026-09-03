# Separating old/new incidence from new/new repair mass

## Original task status

The conjecture remains unresolved. `Submission/Spec.lean` is unchanged with
its original `sorry`. No proof or disproof has been submitted.

## Checked results

`OldNewRepairSplitExplore.lean` and `CompletionSelfMassExplore.lean` compile
and have current oleans. `OldNewRepairSplitAudit.lean` checks 12 declarations;
its saved output in `OldNewRepairSplitAudit.log` contains only `propext`,
`Classical.choice`, and `Quot.sound`.

### Exact finite split

For disjoint finite A,F and any target finset T, define

    selfMass(F,T) = sum_(n in T) r_F(n).

The checked identity is

    incrementMass(A,F,T)
      = 2 sum_(x in F) targetDegree(A,T,x) + selfMass(F,T).

Unlike the previous completed-set degree identity, this isolates the OLD
set in the degree and keeps every new/new representation in a separate term.
Also selfMass(F,T) <= |F|^2.

If every target gains at least delta L, R>0, and

    R targetDegree(A,T,x) <= H |T| L   for every x in F,

then

    [delta - 2H |F|/R] |T| L <= selfMass(F,T).

There is no independence, packet-shape, or reuse hypothesis.

### Negligible additions

For sequences with |F_k|/R_k -> 0 and the displayed old-degree bounds,
for every fixed d<delta, eventually

    d |T_k| L_k <= selfMass(F_k,T_k),
    sqrt(d |T_k| L_k) <= |F_k|.

If in addition r_(F_k)(n) <= epsilon_k L_k on all targets in T_k,
where epsilon_k -> 0 and delta>0, then T_k is eventually empty.
Thus one cannot silently require the new/new contribution to remain
uniformly subscale while using this bounded-old-degree repair mechanism.

### Infinite set completion

For A subset B with the same normalized counting limit, the previous
counting difference theorem makes count(B\\A,N)/R(N) tend to zero. The
new results transfer the finite split to exact cutoffs and prove

    d |T_N| L(N) <= sum_(n in T_N) r_(B\\A)(n)

and

    sqrt(d |T_N| L(N)) <= count(B\\A,N)

under the explicitly stated old-set degree and target-deficit hypotheses.

For a hypothetical nonzero logarithmic-limit completion B, the checked
Tauberian theorem supplies its count/sqrt(N log N) limit. If A already has
the same count limit and its OLD target degrees satisfy the displayed bound,
persistent delta log N deficits force, for every d<delta, arbitrarily large
N with some n in T_N such that

    r_(B\\A)(n) >= d log N.

The addition must therefore supply logarithmic self-representation peaks,
even though it has negligible normalized counting mass.

## Application check and remaining gap

The old-set degree hypothesis is NOT proved for the exceptional target sets
of the existing probabilistic base. Power-saving target counts, local
difference sparsity, and individual triple-intersection bounds do not by
themselves establish it.

Nor are the new/new obligations a contradiction. Negligible counting mass
does not imply uniformly sublogarithmic self-representations; the existing
sparse-packet examples already demonstrate that sparse sets can have large
peaks. In the illustrative power-count regime |T_N| about N^(1-alpha), the
square-root obligation has size about N^((1-alpha)/2) sqrt(log N), still
little-o of sqrt(N log N) for every fixed alpha>0. This scaling observation
is not an existence theorem for an efficient additive basis of T_N.

A genuine shared repair still needs either concentrated old-set incidences
or an efficient new/new cover of the exceptional targets, with all collateral
counts controlled. Neither has been constructed here. The finite graph
patching results also still lack a cross-scale integer realization. No
cutoff-independent finite-prefix feasibility theorem or universal
contradiction settling the original conjecture has been obtained.
