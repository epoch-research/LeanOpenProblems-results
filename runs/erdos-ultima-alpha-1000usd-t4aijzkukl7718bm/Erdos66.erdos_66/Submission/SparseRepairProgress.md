# Summable repairs and a sparse-exception completion theorem

The conjecture in `Spec.lean` remains unchanged, unproved, and undisproved.
No submission has been made.

## New checked files

* `ClippedRepairExplore.lean`: clip a single target correction just below
  c*log(n+2), with additive error less than 2, without overshooting the
  maximum of the old count and the target profile.
* `RepairChainExplore.lean`: summable-error iteration for a monotone chain
  of finite repairs, with no extra support-growth assumption.
* `SparseRepairExplore.lean`: construct the chain and prove its union is a
  witness provided a sufficiently sparse-exception base set is supplied.
* `SparseRepairAxiomCheck.lean`: the three main results depend only on
  propext, Classical.choice, and Quot.sound.

All three main files compile and have built oleans.

## Exact conditional theorem

`Erdos66SparseRepair.sparse_exception_completion` states:

For c>0 and K,C>=0, there exists a threshold function T : Nat -> Nat,
chosen before the target sequence and base set, such that:

If n_k>=T(k), A has the global envelope

    r_A(z) <= K + C*log(z+2),

has asymptotic upper bound c, and has asymptotic lower bound c outside
range(n), then there is B containing A with

    r_B(z)/log(z) -> c.

The hypotheses of asymptotic upper/lower bounds are written using
`forall epsilon>0, eventually ...`, and the lower bound includes the
condition `z not in Set.range n`.

## Iteration details

Set allowance(k)=2^(-k-1), budget(k)=1-2^(-k), residual(k)=2^(-k).
A choice-and-recursion construction yields increasing S_k and finite F_k
with S_0=A, S_(k+1)=S_k union F_k, and

    r_(S_(k+1))(z)
      <= max(r_(S_k)(z), c*log(z+2)) + allowance(k)*log(z+2).

The common envelope used for the uniform single-repair thresholds is
K+(max(C,c)+1)*log(z+2). The finer induction invariant uses budget(k)
instead of 1.

For fixed J and z the increasing union satisfies

    r_(union S_k)(z)
      <= max(r_(S_J)(z), c*log(z+2)) + residual(J)*log(z+2).

Every representation count of a monotone union is attained at a finite
stage, because only finitely many elements <=z are relevant.

For fixed J, S_J differs from A by finitely many points; its excess count
is bounded by 2*sum_(k<J)|F_k|. Therefore the union preserves the
asymptotic upper bound c. Each exceptional target is repaired up to an
additive error below 2, proving the lower bound. The file also proves
log(z+2)/log(z)->1 and converts to the denominator in the conjecture.

## What is still missing

No base set with these sparse exceptional targets has been constructed.
The finite power annuli leave dense intervals of uncontrolled targets.
Arbitrary countable exceptional sets cannot be re-enumerated to meet an
arbitrarily fast threshold sequence. Nor does partitioning an exceptional
set into sparse subsequences justify a countable iteration preserving all
eventual lower bounds. These would be invalid quantifier interchanges.

The completed theorem is a conditional reduction, NOT a solution to the
original existential statement and NOT a disproof.
