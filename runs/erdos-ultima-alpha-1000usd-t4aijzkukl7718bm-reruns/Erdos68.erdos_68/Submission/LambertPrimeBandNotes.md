# Prime-band congruences (not a solution of Erdős 68)

`Submission/LambertPrimeBand.lean` compiles and its printed axiom checks use
only `propext`, `Classical.choice`, and `Quot.sound`.

Write

    A_m = sum_(d|m, d>=2) m!/(d!)^(m/d),
    M_n = product_(p prime, n/2 < p <= n) p.

## New Lean-verified statements

* `lambertCoeff_modEq_prime_band`: A_m = 1 modulo every prime p with
  p <= m < 2p.
* `primeBandProduct_dvd_lambertCoeff_sub_one`: M_m divides A_m-1.
* `primeBandProduct_dvd_lambertCorrectionPrefix`: M_n divides

      H_n = sum_(m=0)^n (A_m-1) * n!/m!,

  where subtraction is natural subtraction (the m=0,1 terms are zero).
* `lambertPrefix_modEq_exponentialPrefix`: putting

      L_n = sum_(m=0)^n A_m * n!/m!,
      E_n = sum_(m=2)^n n!/m!,

  one has L_n = E_n modulo M_n. The exact identity L_n=E_n+H_n
  is also verified as `lambertPrefix_split`.

For the coefficient congruence, every proper divisor d of m satisfies
2d<=m, hence d<p. Thus p divides m! and is coprime to (d!)^(m/d).
Each proper-divisor contribution vanishes modulo p, leaving the d=m term 1.
For the prefix congruence, split at m=p. Before p the factor n!/m! is
itself divisible by p; from p onward the coefficient A_m-1 is divisible by p.
Distinct primes can then be multiplied.

## Why this does not yet give irrationality

The Lambert scaled tails are not small. The previously verified theorem
`factorial_lambert_tail_large` already rules out the linear tail bound in the
integer-descent criterion. The new congruences do not give a usable bound
on the residue of these large tails modulo M_n, and they do not transfer
unchanged to the rowwise floor coefficients.

In particular this file proves no infinite-change result for the factorial
carries and no divergence result for the grid approximants' denominators.

## Additional obstruction: rational comparison coefficients

The following construction is mathematical reasoning, **not a Lean-verified
result**. It shows why the new congruences plus coefficient asymptotics alone
still cannot settle the target. It does not change the exact A_m in the
conjecture.

Let alpha be the target series and delta=3/2-alpha, so 0<delta<1/4 by the
existing verified interval. For even n>=4 take the positive weights

    w_n = (n-1) M_n / n!.

These tend to zero: M_n is at most the primorial of n, which is at most 4^n.
Starting with remainder delta, subtract g_n*w_n at each even index, where
 g_n is the floor of the current remainder divided by w_n. The new remainder
is in [0,w_n); thus the remainders tend to zero and

    delta = sum_(n>=4, n even) g_n*w_n.

Set C_n=A_n+(n-1)M_n*g_n at even n>=4, and C_n=A_n otherwise. Then

* C_n are nonnegative integers and sum C_n/n! = 3/2;
* C_n=A_n at every prime index and every odd index;
* C_n=1 modulo n-1, and C_n=1 modulo M_n;
* the same prefix prime-band congruences follow by the same split at m=p;
* C_n/A_n tends to 1.

For the last claim, for even n>=6 the previous remainder is less than w_(n-2),
so

    0 <= C_n-A_n < n(n-1)(n-3) M_(n-2) <= n^3 * 4^(n-2).

Meanwhile A_n>=n!/2^(n/2). Their ratio tends to zero. At odd indices the
perturbation vanishes. At n=4 the digit is zero because w_4=3/8>delta.

This comparison construction does not refute any statement about the exact
coefficients A_n. It only prevents treating the newly established
congruences and asymptotic size by themselves as an irrationality proof.

## Status

The original conjecture remains unproved and undisproved in this work.
`Submission/Spec.lean` is unchanged, and no proof has been submitted.
