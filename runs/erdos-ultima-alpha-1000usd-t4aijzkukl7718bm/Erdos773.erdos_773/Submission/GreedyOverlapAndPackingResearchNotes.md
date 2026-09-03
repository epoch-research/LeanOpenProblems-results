# Duplicate errors, witness packing, and common residual neighbors

This is NOT a settlement of Erdős 773. The main conjecture remains admitted
for 0<epsilon<=1/3, and no actual Sidon lower exponent or endpoint improved.
The strongest actual lower bound is still

    eventually M(N) >= (5/4) N/(N log N)^(1/3).

## Verified modules

* GreedyOverlapError.lean: 8 printed audits (from the preceding continuation).
* GreedyWitnessPacking.lean: 6 printed audits.
* GreedyCommonNeighbors.lean: 6 printed audits.
* GreedyErrorCertificates.lean: 3 printed audits.

All are built and admission-free. GreedyConfigurationTails also now exports
`markov_bound`, increasing its printed-audit count from five to six. None of
these modules imports the admitted Spec theorem. The combined audit with
GreedyHypergraphState and StoppedGreedyMoments has 47 printed checks:

    /tmp/greedy-overlap-packing-final-audit.log

Every audit uses only propext, Classical.choice, and Quot.sound. The modules
compile without warnings.

## Duplicate correction: linear-in-edge-count bound

Let H be four-uniform with pair codegrees at most K and intersections of
distinct edges at most two. The existing ordered overlap family satisfies

    |overlaps(H)| <= 6 |H| K.

Choose the first edge, one of its six vertex pairs, and a second edge
containing that pair. This improves the earlier V^2 K^2 bound and is useful
after the many-copy regularization construction.

For an ordered overlap (e,f), its witness is the symmetric difference
(e\f) union (f\e), which has exactly four vertices. If two original edges
have the same residual pair after selecting I, their witness is in I.
Repeated witnesses with different edge-pair indices retain their multiplicity.

Define overlapCost(H,I) as the number of selected indexed witnesses, and
totalExcess(H,I) as the sum of residual-two-edge duplicate corrections over
available vertices. The checked bounds are

    totalExcess(H,I) <= 2 overlapCost(H,I),
    totalExcess(H,J) <= 2 overlapCost(H,I)     for J subset I.

For the stopped process with selection floor L>0, put p=t/L. Its previously
proved inclusion bound gives

    E_t overlapCost <= 6 |H| K p^4,
    E_t totalExcess <= 12 |H| K p^4,
    E_t 1_{exists J subset I: totalExcess(H,J)>B}
        <= 12 |H| K p^4/B                       (B>0).

For a D-regular hypergraph on V vertices, 4|H|=VD, so the last bound is
3VDKp^4/B. With D>0, V>0, K<=D^(1/100), p<=D^(-1/3+1/100), and
B=V D^(-1/100), `prefix_error_power_tail` gives 3D^(-41/150).
This is an error tail, not an early-stop bound.

## Generic packing and exponential tails

For indexed nonempty supports C(i), i in T, assume

    |C(i)| <= r,
    #{i in T : a in C(i)} <= M          for every vertex a.

`packing_bound` proves that some pairwise disjoint U subset T has

    |T| <= r M |U|.

The proof takes a maximum disjoint subfamily. Every support intersects a
member of that subfamily, and incidence counting bounds the cover size.
The index map need not be injective.

If each support also has at least s vertices, t<=L, and more than rMk
supports lie in the selected state, a disjoint selected (k+1)-subfamily exists.
Its union has at least s(k+1) vertices. Applying the inclusion bound to
these unions and summing over subfamilies gives `packing_tail`:

    E_t 1_{selected support count > r M k}
        <= choose(|T|,k+1) p^(s(k+1)).

No independence of witness events is assumed.

`choose_mul_pow_le` retains the crucial factorial saving:

    choose(m,j) p^(s j) <= (3 m p^s/j)^j      (j>0, p>=0).

It follows directly from the exponential-series bound
j^j/j! <= exp(j) <= 3^j. Consequently the packing tail is at most

    (3 |T| p^s/(k+1))^(k+1).

## Residual common-neighbor witnesses

Fix distinct designated endpoints u,v. A pattern consists of original edges
e,f and a shared vertex w, with u,w in e and v,w in f, w distinct from u,v,
v not in e, and u not in f. Its selected witness is

    (e\{u,w}) union (f\{v,w}).

Assuming degree(u)<=D, the verified combinatorial bounds are:

* at most 3 D K indexed patterns;
* witness size between 3 and 4;
* each vertex belongs to at most 4 K^2 indexed witnesses.

For the last bound, occurrences in the first role are at most 2K^2: choose
an edge through u and the given witness vertex (at most K), choose w among
its two other vertices, then choose f through v,w (at most K). The second
role contributes the same bound by swapping endpoints and edges. The size
lower bound uses the intersection-at-most-two hypothesis and the shared
vertex w, which is outside both selected residual supports.

If u,v are available and w lies in closes(u) intersect closes(v), some
pattern with center w has its entire witness selected. Thus the actual
common-neighbor count is at most the selected pattern count. Pattern counts
are monotone in the selected set, so they control all selected subsets,
including all prefixes while u and v remain available.

`prefix_common_tail` and `prefix_common_exponential_tail` prove

    E_t 1_{some such subset has commonDegree(u,v)>16 K^2 k}
      <= choose(3DK,k+1) p^(3(k+1))
      <= (9 D K p^3/(k+1))^(k+1).

The statement requires t<=L; it is not silently applied when p>1.

## Simultaneous actual trajectory certificate

`controlled_run` combines the duplicate tail and all ordered distinct
endpoint pairs. If

    12 |H| K p^4/B + V^2 (9 D K p^3/(k+1))^(k+1) < 1,

there is an actual reachable independent state I such that

    |I|=t OR Q(I)<L,

and, for every J subset I:

* totalExcess(H,J)<=B;
* every distinct available u,v has commonDegree(H,J,u,v)<=16K^2 k.

`controlled_regular_run` replaces the first probability term by 3VDKp^4/B
for regular H. The proof uses finite expectation attainment and a union
bound. It does not assume a hypothetical state satisfying the estimates.

## Remaining gap

Neither control prevents Q from dropping below L. No concentration theorem
for the evolving local degrees, no differential-equation tracking, and no
long-running-time theorem has been proved. The expected heuristic profiles
q=exp(-D(t/V)^3) and the corresponding d2,d3,d4 remain unproved targets.

Even a successful logarithmic-gain extraction would remain at the 2/3
exponent scale. It would not by itself settle the near-linear conclusion
for every fixed epsilon>0. No new square-specific selection or fixed-power
upper bound was found in this continuation.

Spec.lean remains unchanged, with SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
Its latest compile log is /tmp/spec-overlap-packing-check.log, still with the
original admission. No proof submission has been made.
