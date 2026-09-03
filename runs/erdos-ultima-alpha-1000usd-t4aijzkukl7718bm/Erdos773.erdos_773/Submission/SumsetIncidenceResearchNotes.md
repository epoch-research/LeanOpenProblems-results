# Sumset-incidence continuation

This does NOT settle Erdos 773. The conjecture and its sole admission in
Spec.lean are unchanged. The strongest actual square-Sidon lower bound remains
GreedySquarePowerLower's explicit positive constant times N^(2/3).

## Verified finite incidence theorem

New module: SumsetIncidence.lean (102 lines).

For finite sets X,Y, an arbitrary bipartite relation R, and K>=0, suppose
all distinct y,z in Y have at most K common neighbors in X. If e is the
incidence count, the module proves

    e^2 <= |X| (|Y|^2 K + e),
    e <= |Y| sqrt(|X| K) + |X|.

The proof counts ordered two-paths exactly, separates diagonal right pairs,
and applies finite Cauchy--Schwarz. All incidences are counted; no unsupported
identification of edges with distinct sum values is made.

The generic API carries a decidability instance for R. This avoids mismatches
between classical decisions for an abstract relation and the concrete
membership decisions when applying the API to natural-number sumsets.

## Sidon-in-sumset bound

New module: SidonInSumset.lean (96 lines).

For a Sidon set S of natural values, the relation x+y in S has no four-cycle:
the four corner values have equal opposite sums, and Sidonness forces either
the two left vertices or the two right vertices to agree. Hence K=1, and

    S subset X+Y  =>  |S| <= |Y| sqrt(|X|) + |X|.

`max_card_le` gives the same upper bound for maxSidonSubsetCard(A) whenever
A subset X+Y. The proof obtains an actual maximizing Sidon subset from the
finite supremum. Coverage only gives |S|<=e, not |S|=e.

The module also proves the version with any uniform nonzero-translate
intersection bound K:

    |{a in S : a+D in S}| <= K for every D>0
    => |S| <= |Y| sqrt(|X| K) + |X|.

To bound common neighbors for y<z, inject x into the translate intersection
by x |-> x+y, with D=z-y. The other order is handled symmetrically.

## Arithmetic obstruction to the proposed disproof route

New module: SquareAdditiveBasis.lean (146 lines).

Use the existing uniform divisor bound from TranslatedSquareFibers:
for every delta>0, there is K_delta>0 such that every nonzero translate
intersection of the first N square values has size <=K_delta N^delta.
The incidence theorem now proves, uniformly over covers by natural sumsets,

    squares(1,...,N) subset X+Y
    => N <= |Y| sqrt(|X| K_delta N^delta) + |X|.

Public API: `finite_cover_bound`.

For balanced bases this implies, for every epsilon>0, eventually for ALL B,

    squares(1,...,N) subset B+B  =>  |B| >= N^(2/3-epsilon).

Public API: `eventual_basis_lower`.

`eventual_exceeds_fixed_power` strengthens the explicit scope: for every
alpha<2/3 and every real C, eventually every such B satisfies

    C N^alpha < |B|.

Thus no basis of size O(N^alpha) with alpha<2/3 exists even along an unbounded
sequence. Such a basis would have been needed for the simplest proposed
C4/sumset fixed-power disproof.

### Unequal summand sets do not repair this certificate

The stronger `eventual_incidence_certificate_lower` proves: for every
epsilon>0, eventually for ALL X,Y covering the squares,

    N^(1-epsilon) <= |Y| sqrt(|X|) + |X|.

Indeed choose delta=epsilon; eventually K_delta N^delta<=N^(2 epsilon),
so its square root is <=N^epsilon. The general square-cover bound then gives
N<=N^epsilon (|Y|sqrt(|X|)+|X|). Exact real-power cancellation finishes.

This says the C4/Sidon upper-bound EXPRESSION ITSELF cannot have a fixed
power saving for any such cover, including unbalanced ones. It does NOT
say that the actual maximum is at least this expression: the actual Sidon
maximum is bounded ABOVE by it. No reversal of this inequality is allowed.

These results concern natural-number summand sets, as their statements say.
No claim about arbitrary integer/real summand sets or stronger incidence
certificates has been formalized. Nor is there a claim that all possible
sumset methods, or all upper-bound methods, are excluded.

## Verification and current state

All three new modules build without warnings or admissions; they total 344
lines. Their .olean files are present. SumsetAudit.lean audits all 14 public
lemmas/theorems, each with precisely the permitted axioms propext,
Classical.choice, Quot.sound. No new module imports the admitted Spec theorem.

Logs:

* /tmp/sumset-incidence.log
* /tmp/sidon-in-sumset.log
* /tmp/square-additive-basis.log
* /tmp/sumset-final-audit.log

Spec.lean was checked again:

    /tmp/spec-sumset-continuation-check.log

It still has its original import, unchanged conjecture statement, and sole
sorry at line 2031 for 0<epsilon<=1/3. SHA-256 remains

    917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

No new original-conjecture exponent bound was obtained, no result was
consolidated into Spec.lean, and no proof or disproof was submitted.
