# Joint sum and difference capacity obstruction

The original square-Sidon conjecture remains unsettled. These auxiliary
counterexamples are ordinary integer sets, NOT sets of squares.

## Checked modules

`IntegerSumCapacity.lean` proves that distinct strict representations of one
sum have disjoint endpoints. The support of g+1 such representations has
size 2(g+1), and the family of forbidden supports in [1,m] has cardinality
at most 2*m^(g+2). Avoiding these supports bounds strict sum multiplicity by
g. For an AP-free carrier and g>=1, the bound includes the possible diagonal
representation as well.

`JointCapacityObstruction.lean` adds these sum obstructions to the existing
finite random-carrier/deletion argument. For n>=1000 and log(n)>=5 it gives
B contained in [1,n^40], with:

* |B| >= n^16/8;
* B is three-term-progression-free;
* every positive difference has at most two increasing representations;
* every sum has at most two unordered representations, including diagonals;
* every Sidon subset of B has cardinality less than n^15.

An integral consequence is

    (maxSidonSubsetCard B)^16 <= 8^15 * |B|^15.

The extra six-support penalty has expectation at most
2*p^6*n^160, where p=1/(4*n^24). The combined difference and sum penalty
is at most 3*n^16/4096, leaving the stated reward margin.

Both modules compile without admissions. The nine printed principal axiom
checks use only propext, Classical.choice, and Quot.sound. Logs:

    /tmp/integer-sum-capacity.log
    /tmp/joint-capacity-obstruction.log

## Scope

This is a fixed carrier-size power gap even under both capacity-two bounds.
It is not a square-set counterexample. At ambient height N^2=n^40, the
carrier has size about N^(4/5), not N^(1-o(1)). The earlier near-critical
ambient-density examples have an explicitly proved difference-capacity
bound; the new sum-capacity conclusion has not been extended to them.

Neither module was added to Spec.lean. The main file retains the exact
conjecture and its sole remaining admission for 0<epsilon<1/3.
