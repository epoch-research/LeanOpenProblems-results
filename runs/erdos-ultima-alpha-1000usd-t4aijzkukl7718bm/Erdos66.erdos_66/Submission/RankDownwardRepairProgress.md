# Exact-bracket downward rank relocation

All six production files compile. `RankDownwardRepairAudit.lean` audits
22 lemmas/theorems; each depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

## Main result

`Erdos66GlobalRankDownwardRepair.uniformly_eventually_downward_rank_repair`
is uniform over exact harmonic-bracket hosts with a fixed logarithmic
representation envelope. Given one target in `[4N,5N]`, at most `M log N`
prescribed upper endpoints can be deleted and relocated within their original
cumulative-rank cells, preserving every original floor/ceiling prefix bracket.

The resulting central representation count decreases by exactly twice the
number of moved endpoints. For every other natural target z, the absolute
change is at most `ε log(z+2)`, eventually in N.

The hypotheses include a central-triple cap for the CURRENT host through
`N^33`, and a margin of `2 ceil(log(N)^8)` above the central midpoint for each
prescribed endpoint. These conditions are not automatically inherited by an
arbitrarily updated host.

## Mechanism

* `RankCellWindowExplore`: each eligible prescribed old point has an entire
  width-`ceil(log(N)^8)` window whose candidate points share its assigned rank.
* `AdaptiveSingletonAlgebraExplore`: a new singleton increases the total
  insertion energy by at most five times an incidence indicator.
* `AdaptiveSingletonSelectionExplore`: one adaptive common exponential
  potential controls all inserted points jointly, avoiding a sum of separate
  worst-case bounds.
* `PrescribedRankRelocationExplore`: selected row coverage identifies the
  assigned deletion set with the prescribed endpoints. This combines exact
  central reduction with original-bracket preservation.
* `LogCellWindowBudgetExplore`: logarithmic candidate-degree estimates and
  the required finite probability budgets hold eventually.
* `GlobalRankDownwardRepairExplore`: finite tests plus the previously proved
  short-support tail estimate cover every off-center natural target.

## What is not proved

This is a one-target theorem, not a simultaneous downward correction theorem.
It does not establish enough eligible endpoints at arbitrary targets. It does
not show that insertions retain triple sparsity for later steps. It does not
repair all of a shrinking-tolerance exceptional set or settle Erdős 66.
`Submission/Spec.lean` still contains the original unproved conjecture.
