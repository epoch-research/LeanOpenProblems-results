# Exact joint L1 regime, including selected scales — original UNSOLVED

`Submission/Spec.lean` is unchanged and retains its original `sorry`.
This continuation supplies no prime-pair lower bound or irrational
counterexample. No incomplete proof was submitted.

New verified file: `Submission/SharpJointSmoothRegime.lean`.
Namespace: `Erdos972SharpJointSmoothRegime`.

## Actual lower bound from prime inputs

For t>0, N>=4, epsilon>0, and

    epsilon <= t(1+log N),

if the logarithmic prime mass in (N/2,N] is at least N/4, then

    smoothL1Error(t,N)/N >= [1-exp(-epsilon/8)]/8 > 0.

Here smoothL1Error is the actual sum of |S_t(n)-Lambda(n)|, not an
upper-bound budget. The needed prime-block mass holds eventually, by
the already proved Chebyshev-form prime number theorem.

The elementary scalar estimate is

    a<=t*x, x>=0, t>0
    => [(1-exp(-a/2))/2]*x <= |(1-exp(-t*x))/t-x|.

It follows by factoring 1-exp(-t*x) at the half argument and using
1-exp(-t*x/2)<=t*x/2. For primes p in the upper block,
log p >= (1+log N)/4. The prime-power Euler-factor formula for S_t then
supplies the actual error lower bound.

## Necessary and sufficient regime

Combined with `JointSmoothL1.lean`, this proves, for every eventually
positive parameter sequence t_N,

    smoothL1Error(t_N,N)/N ->0
       iff t_N(1+log N)->0.

The file also proves the same equivalence along arbitrary diverging
cutoffs N(i), over an arbitrary index filter. Thus a selected irrational
good-scale sequence does not evade the necessity statement. The input
bound and parameter are allowed to depend on the same index.

Principal results:

* `normalized_error_lower`
* `small_parameter_of_l1`
* `joint_l1_iff`
* `small_parameter_of_l1_along`
* `joint_l1_iff_along`

## Consequence for the existing absolute divisor-tail method

`damping_of_l1` and `damping_of_l1_along` show that any such L1-approximating
sequence, with divisor cutoffs D(i)<=N(i) eventually, satisfies

    exp(-t(i)*log D(i)) ->1.

`l1_damping_incompatible` explicitly rules out simultaneous normalized
L1 convergence to zero and convergence of this damping factor to zero
(on a nontrivial index filter).

This blocks parameter optimization of that particular L1-plus-vanishing-
damping argument, not every smoothing or signed-tail method. The result
is about the damping factor; it is NOT a lower bound on the actual signed
divisor tail and is NOT a disproof of the original conjecture.

All eight principal declarations compile and their axiom audits contain
only `propext`, `Classical.choice`, and `Quot.sound`.
