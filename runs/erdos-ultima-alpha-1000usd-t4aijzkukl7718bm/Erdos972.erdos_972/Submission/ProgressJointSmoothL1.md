# Sharper joint-parameter L1 approximation — original still UNSOLVED

`Submission/Spec.lean` remains unchanged with its original `sorry`.
No prime-pair lower bound, sufficient signed off-diagonal estimate, or
irrational counterexample has been proved. No incomplete proof was submitted.

## New file

`Submission/JointSmoothL1.lean`, namespace `Erdos972JointSmoothL1`.

Use the existing positive divisor function

    A_t(n) = sum_{d|n} mu(d) exp(-t log d)

and the corrected smooth Mangoldt function S_t=(A_t-A_0)/t.
The new genuine pointwise majorant is

    F_t = A_t * Lambda = (mu(n) n^(-t)) * log,

where * is Dirichlet convolution. For t>=0, F_t>=Lambda, and for t>0,
S_t<=F_t. This is not the earlier bounded fixed-t proxy alone.

## Verified differential and finite-sum bounds

* The derivative of A_t is A_t * (Lambda(n)n^(-t)), a nonnegative
  convolution for t>=0.
* H_N(t)=sum_{1<=n<=N} A_t(n)/n satisfies

      H_N(0)=1,
      H_N'(t)<=14(1+log N) H_N(t).

  Gronwall gives H_N(t)<=exp(14t(1+log N)), for every N>0,t>=0.
* The actual nonnegative majorant excess satisfies

      sum_{n<=N}(F_t(n)-Lambda(n))
        <=7N[exp(14t(1+log N))-1].

  This uses the positive convolution (A_t-delta_1)*Lambda and the
  elementary Chebyshev bound psi(x)<=7x.
* Prime powers contribute a deficit bounded by t Lambda(n) log n.
  All other terms satisfy S_t(n)<=F_t(n)-Lambda(n). Consequently,

      sum_{n<=N}|S_t(n)-Lambda(n)|
        <=7N[exp(14z)-1+z],  z=t(1+log N).

## Principal declarations

* `harmonic_mass_bound`
* `majorant_excess_sum_bound`
* `joint_l1_bound`
* `joint_l1_tendsto`
* `joint_l1_regime_damping`

The joint limit theorem proves normalized L1 convergence to zero whenever
`t_N>0` eventually and `t_N(1+log N)->0`. This improves the available
ONE-VARIABLE regime: no extra power of log N or divisor-cardinality
factor is needed in this normalized L1 statement.

Every principal theorem compiles and its printed axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Essential limitations

This is NOT an improved two-variable Mangoldt correlation estimate. A
naive multiplication by the other Mangoldt weight costs another log N.
No same-scale lower bound for the smoothed pair correlation has been
proved in this joint regime.

`joint_l1_regime_damping` also proves that in this regime, for every
D_N<=N eventually,

    exp(-t_N log D_N) -> 1.

Thus this sharper L1 approximation still cannot simply be combined with
the existing absolute divisor-tail estimate that requires this damping
factor to vanish. This conclusion concerns the factor, not a lower bound
on the actual signed tail. The original arithmetic gap remains open.
