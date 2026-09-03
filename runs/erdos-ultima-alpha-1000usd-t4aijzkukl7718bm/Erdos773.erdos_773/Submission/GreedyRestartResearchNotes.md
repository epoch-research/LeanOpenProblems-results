# Greedy restart: exact mixed-residual extension certificate

## Main task remains unresolved

Spec.lean is unchanged, with its sole admission for 0 < epsilon <= 1/3.
No new actual asymptotic lower exponent, coefficient-one endpoint, or
unrestricted fixed-power upper bound was obtained. The strongest completed
actual lower bound is still eventual M(N) >= N^(2/3)/36.

No incomplete submission was made in this continuation. The earlier rejected
incomplete submission remains rejected.

## New clean module

Submission/GreedyRestartAlteration.lean imports the clean modules
GreedyHypergraphState and PenalizedAlteration, not Spec. It compiles without
warnings or admissions. All six printed axiom audits use only propext,
Classical.choice, and Quot.sound.

Namespace: Erdos773.GreedyRestartAlteration

## Exact residual system

For an independent set I in a four-uniform hypergraph H, let Q be the available
vertex set. The residual system consists of every e \\ I for e in H for which
that residual is wholly contained in Q. Equal residual supports may be
identified for the purpose of independence.

extension_iff proves, for J subset Q,

    I union J is independent in H
        iff J avoids every residual support.

residual_size proves that every such support has size 2, 3, or 4. In particular,
restarting on the original four-edges contained in Q is not equivalent to a
legal extension: the contracted two- and three-edges must be retained.

## A genuine finite extension bound

Let E_j be the number of ORIGINAL active edge indices with residual size j.
For every p in [0,1], extend proves existence of J subset Q such that I union J
is independent and

    |I union J| >= |I| + p|Q| - p^2 E_2 - p^3 E_3 - p^4 E_4.

No old selected vertex is discarded. indexed_cost proves the exact indexed
sum decomposition. residual_cost_le handles repeated residual supports in
the correct direction: identifying supports can only decrease the deletion
budget. The extension follows from finite Bernoulli alteration, not from an
assumed long stochastic trajectory.

This is an unconditional finite hypergraph certificate. It has not been
instantiated to yield a stronger asymptotic square-Sidon bound.

## One-shot mean-field accounting

The dimensionless ideal-profile reward is defined as

    modelReward(t,z) = t+z-(3/2)t^2 z^2-t z^3-z^4/4.

The terms of degrees 2, 3, and 4 are all retained. For t>0 and z>=0,
model_reward_upper proves

    modelReward(t,z) <= t + 1/(6t^2).

The quadratic estimate follows by completing the square; the cubic and
quartic terms are nonpositive in the reward. This bounds ONLY this numerical
lower-bound certificate. It is NOT an upper bound on the actual independence
number, on possible extensions, or on M(N). It does not rule out more
sophisticated restarts or exchanges.

At t of order (log N)^(1/3), the maximum extra physical time certified by this
single alteration step is of order (log N)^(-2/3), not a fixed multiplicative
gain in t. Thus the simplest fill-and-restart proposal does not close the
coefficient-one endpoint, much less improve the exponent.

## A possible further program, not proved

One could try to regularize a MIXED residual hypergraph between stochastic
stages, transferring independent-set density at each regularization. This
would require new results: simultaneous rank-2/3/4 regularization with
suitable local overlap bounds, a shifted-time mixed-degree trajectory theorem,
and quantitative first-crossing estimates for the new short edges.

Ordinary disjoint-copy regularization does not automatically reset existing
common-neighbor irregularities. In particular, the old four-uniform selected-
witness tail laws cannot simply be reused for newly added rank-two edges,
whose relevant witnesses are already present at the start of a stage. No
successful bootstrap or coefficient improvement is claimed.

Even an optimal generic four-uniform extraction theorem would not by itself
settle the smaller-epsilon range of Erdős 773; a further square-specific input
would still be required.

## Verification

Build and audit log: /tmp/greedy-restart-alteration.log
Olean: .lake/build/lib/lean/Submission/GreedyRestartAlteration.olean

Spec SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
