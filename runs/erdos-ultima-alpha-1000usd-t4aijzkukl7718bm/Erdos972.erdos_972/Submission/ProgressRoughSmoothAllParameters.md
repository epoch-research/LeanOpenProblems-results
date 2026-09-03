# Exact rough-smooth lower bound for all parameters — still not a settlement

The original `Submission/Spec.lean` is unchanged and retains its `sorry`.
No prime-pair infinitude proof or irrational counterexample has been found.

## New verified file

`Submission/RoughSmoothAllParameters.lean`
Namespace: `Erdos972RoughSmoothAllParameters`.

This extends the preceding rough-output lower-bound argument from
0<tau<=1/2 to EVERY tau>0. It also compares the resulting exact lower
envelope to the available least-factor error budget for all these choices.

Let Z=fastRoot(u), N=u^6, J=layerCount(u), and

    t = tau/log Z,
    C = Erdos972EfficientPrimeAlmostPrime.roughConstant,
    c_exact(tau) = (1-exp(-tau))^49153/(8195*tau*C),
    E(alpha,tau,u)
      = t*log(floor(alpha*u^6)) * (100000*u^6*(J+1)).

### Pointwise and finite lower bounds

`rough_smooth_lower_exp` proves, for t>0, n>1, Z>1, n coprime to Z!,
and Omega(n)<=K,

    (1-exp(-t*log Z))^K/t <= smoothMangoldt(t,n).

There is no small-parameter hypothesis. This uses the exact Euler product,
not a Taylor approximation. `mixed_lower_from_rough_exp` sums this bound
over genuine prime inputs with certified rough outputs.

`rough_weight_to_smooth_exp` applies the already proved rough-output weight
lower bound and gives

    c_exact(tau)*N <= mixedPrimeSmooth(t,alpha,N)

for EVERY tau>0 at any scale satisfying that weight lower bound and the
usual size conditions Z>=2 and alpha<=Z.

### All-parameter comparison

For b=1-exp(-tau), one has 0<b<=1 and b<=tau. Hence, since K=49153>=2,

    b^K <= b^2 <= tau^2,
    c_exact(tau) <= tau.

For alpha>=1 and Z>=2, log(floor(alpha*u^6))>=log Z and J+1>=1. The file
therefore proves the STRICT inequality

    c_exact(tau)*N < E(alpha,tau,u)

for EVERY tau>0 (`all_parameters_lower_envelope_lt_budget`).

This compares a lower envelope with an upper error budget. It does NOT
prove that the actual error is large or that the actual smoothed sum is
small. It rules out only the direct deduction obtained by subtracting
this available error budget from this exact rough-output lower envelope.

### Same-scale quantifiers

`exists_all_parameter_estimates` proves that for every alpha>1 irrational
and B, there is a single u>B with J>B, Z>=2, alpha<=Z, such that for ALL
tau>0 simultaneously:

    c_exact(tau)*N <= mixedPrimeSmooth(t,alpha,N),
    |mixedPrimeSmooth(t,alpha,N)-mixedPrimeMangoldt(alpha,N)| <= E(alpha,tau,u),
    c_exact(tau)*N < E(alpha,tau,u).

This invokes `exists_common_rough_moment_scale`; it does not identify two
independently selected scales or exchange a limit with a parameter choice.

## Verification

The new file compiles to
`.lake/build/lib/lean/Submission/RoughSmoothAllParameters.olean`.
The four principal declarations were axiom-audited and use only propext,
Classical.choice, and Quot.sound. The file contains no sorry declarations.

## Remaining arithmetic gap

Parameter optimization of this lower-bound/comparison pair alone does not
settle the conjecture, even with the exact Euler-product factor and the
full positive parameter range. A genuinely stronger arithmetic lower bound,
signed-correlation estimate, or actual irrational counterexample is still
required. No completed candidate was submitted.
