# Joint capacities at near-square-root ambient density

The original Erdos 773 conjecture remains UNSETTLED. Spec.lean was not edited;
its sole admission remains at line 17287 for 0 < epsilon < 1/3. Its verified
unconditional endpoint is still M(N) >= N^(2/3) eventually.

## New verified module

Submission/NearCriticalJointCapacity.lean imports only the clean
NearCriticalCapacityObstruction and IntegerSumCapacity modules. It does not
import Spec. Its five printed principal audits use only propext,
Classical.choice, and Quot.sound. The module builds without warnings or
admissions and has a built olean.

Namespace: Erdos773.NearCriticalJointCapacity.

For every epsilon > 0, near_critical_obstruction proves there is a FIXED
positive integer g such that, for every sufficiently large parameter n,
there are N >= n and B contained in [1,N^2] with

    |B| >= N^(1-epsilon),
    B is three-term-arithmetic-progression-free,
    every positive difference has at most g increasing representations,
    every sum has at most g unordered representations INCLUDING diagonals,
    maxSidonSubsetCard(B)^5 <= N^4.

These are ordinary integer VALUE sets, NOT sets asserted to consist of squares.
The result closes the previously unproved joint-capacity extension of the
near-critical generic examples. It is not a square-specific counterexample.

The finite polynomial statement, for k>=1 and sufficiently large n, is

    B contained in [1,n^(100k)],
    n^(50k-1) <= 8|B|,
    both capacities <=25k,
    every Sidon subset of B has size <n^(40k).

Taking N=n^(50k), absorbing the factor 8 by n>=8, and choosing k from epsilon
provides the stated quantifiers. Heights are unbounded; examples at EVERY
integer height N are not asserted.

## Proof change

Combine the difference and sum forbidden support families. Each support has
2(g+1) vertices, and the union has at most 3*m^(g+2) members in [1,m]. The
existing Bernoulli reward also penalizes APs and large Sidon subsets.

Put u=R^50=n^(2g) and p=1/(4un). The mass is u/(4n), the AP deletion cost
is at most (u/n)/64, and the cost of ONE unit of the capacity estimate is
at most (u/n)/64. Its new coefficient is three. The large-Sidon penalty
cost is at most one, while u/n>=16. Thus the same final mass u/(8n) survives:

    1/4 - 1/64 - 3/64 - 1/16 = 1/8.

No stronger extraction theorem or extra probabilistic assumption is used.
AP-freeness lets the unordered sum bound include a possible diagonal pair.

## Relevance and limit

A rainbow-pair selection argument cannot rely ONLY on both multiplicity
bounds, AP-freeness, and near-square-root ambient density to infer a
near-linear Sidon subset of an arbitrary integer carrier. A successful
argument for squares must use additional arithmetic structure or a specially
chosen carrier.

This does NOT imply an upper bound for the Sidon maximum of the first N
squares, and it does NOT improve its known lower exponent. No new near-linear
square-specific selection principle was found in this continuation. Digit,
rotation, and fiber considerations were not promoted to unproved hypotheses.

Logs:

* /tmp/near-critical-joint-capacity.log
* /tmp/near-critical-joint-capacity-build.log

Main-file SHA-256 is unchanged:
257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940.
