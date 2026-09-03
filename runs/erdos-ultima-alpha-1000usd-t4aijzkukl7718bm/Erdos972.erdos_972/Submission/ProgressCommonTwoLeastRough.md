# Common two-least comparison and rough lower bound — no settlement

Spec.lean is unchanged and retains the original sorry. No sufficient prime-pair
lower bound or irrational counterexample has been found. No incomplete proof
was submitted.

New file: CommonTwoLeastRough.lean.
Namespace: Erdos972CommonTwoLeastRough.

The file compiles, and the three principal declarations have axiom audits
containing only propext, Classical.choice, and Quot.sound.

## Same-scale result

exists_common_rough_twoLeast_scale repeats the actual direct rational-
approximation scale selection with BOTH of the following at the SAME u:

    primeTwoLeastFactorMoment(alpha,u^6)
      <= 10^9 u^6 log(layerCutoff(u)),

    u^6/[roughConstant*(1+log(u+1))]
      <= coprimePrimeWeight(alpha,fastRoot(u)!,u^6).

It also records the fourth-root cutoff condition needed by the two-least
factor estimate. The original least-factor scale theorem is not used as
though it exposed row data that its conclusion does not contain.

## Every positive parameter

Let

    t = roughParameter(tau,u) = tau/log(fastRoot(u)),
    E2(tau,u) = 10^9 t u^6 log(layerCutoff(u)),
    c(tau) = exactRoughCoefficient(tau).

exists_all_parameter_twoLeast_estimates proves that for each alpha>1
irrational and B, one u>B, with layerCount(u)>B, supports ALL of the following
for EVERY tau>0 simultaneously:

    c(tau) u^6 <= mixedPrimeSmooth(t,alpha,u^6),
    mixedPrimeSmooth(t,alpha,u^6)-E2(tau,u)
      <= mixedPrimeMangoldt(alpha,u^6),
    c(tau) u^6 < E2(tau,u).

The second inequality is one-sided, as in PrimeTwoLeastFactorScales. No
absolute-error estimate is claimed.

## Why the strict comparison holds

The existing cutoff inequalities give

    log(fastRoot(u)) <= log u <= 832 log(layerCutoff(u)).

Consequently E2(tau,u) is strictly larger than tau*u^6 for every tau>0.
The already proved scalar bound c(tau)<=tau then gives the last inequality.
This argument covers every positive parameter, not merely a small-parameter
Taylor regime.

## Scope

This rigorously rules out obtaining a positive lower bound by subtracting
this available error budget from this rough-output lower envelope. It does
NOT say that the actual error is large, nor that the actual smoothed
correlation is small. It is not a disproof of the original conjecture.
A genuinely stronger lower bound or signed estimate remains necessary.
