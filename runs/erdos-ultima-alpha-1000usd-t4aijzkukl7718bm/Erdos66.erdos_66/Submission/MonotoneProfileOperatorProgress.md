# A uniform finite rounding operator for bounded monotone profiles

## Original conjecture status

The conjecture in Submission/Spec.lean remains unresolved. Spec.lean is
unchanged and no proof has been submitted.

## New unconditional theorem

MonotoneProfileOperatorExplore.lean proves

    Erdos66MonotoneProfileOperator.exists_bounded_monotone_rounding_operator.

For c,delta>0, W>=1, and every lower bound N0, it returns M>N0, M>1, and
ONE map Phi from real sequences to finite subsets of [0,M). The map is
chosen BEFORE the profile. It has the following properties:

* If f and g agree below L, Phi(f) and Phi(g) agree below L.
* Their representation counts below L are then exactly equal.
* For EVERY f with 1<=f(x)<=W on [0,M), antitone on that interval,

      |r_{Phi(f)}(n)/log M - c normConv(M,f,n)| <= delta

  at EVERY natural target n, where

      normConv(M,f,n)
        = (1/M) sum_{0<=x<M, x<=n, n-x<M} f(x) f(n-x).

No bound on the number of changes or distinct values of f is imposed.
Prefix agreement holds for arbitrary input profiles, not only admissible
monotone ones, because membership at x depends only on f(x).

## Finite grid and causal realization

Choose

    e = min(1, delta/[100(c+1)(W+1)^2]),
    J = ceil((W-1)/e),
    gridWeight(j) = 1+e*j,  0<=j<=J.

The bin at x is min(J,ceil((f(x)-1)/e)). For 1<=f(x)<=W,

    f(x) <= gridWeight(bin(x)) <= (1+e) f(x).

One fixed palette member C_j is chosen for each grid height. The output is

    Phi(f) = {x<M : x mod M belongs to C_{bin(x)}}.

This formula proves prefix causality directly. Since the bin index is
antitone, each of its fibers is an integer interval (empty fibers are
placed at [0,0)). There are at most J+1 such intervals, independently of M
or the number of changes in f. The existing same-modulus assembly theorem
therefore applies.

## Exact convolution and error accounting

StepConvolutionBridgeExplore.lean proves that the geometric weighted overlap
profile is EXACTLY normConv of its step function. It includes the clamped
empty-interval cases and every natural target; no continuous approximation
is silently substituted.

BoundedProfileQuantizationExplore.lean proves

    0 <= normConv(M,f,n) <= W^2,
    |normConv(M,g,n)-normConv(M,f,n)| <= (R^2-1)W^2

when 0<=f<=W and f<=g<=Rf on [0,M), R>=1.

UniversalHeightPaletteExplore.lean extracts one list C_j that works for ALL
subsequently chosen interval geometries. It follows from the checked
prefix-extension system by prescribing all pieces as old; the returned
superset must then equal that prescribed assembly inside [0,M).

Use error delta/2 for this fixed-height palette and the multiplicative
quantization bound with R=1+e for the other delta/2. Thus both the palette
and the rounding rule are independent of the eventual monotone profile.

## Verification

All five new production files compile and have built oleans:

* MonotoneIntervalFibersExplore.lean
* StepConvolutionBridgeExplore.lean
* UniversalHeightPaletteExplore.lean
* BoundedProfileQuantizationExplore.lean
* MonotoneProfileOperatorExplore.lean

MonotoneProfileOperatorAudit.lean checks the principal declarations. Only
propext, Classical.choice, and Quot.sound occur. The production files have
no sorries or new axioms. MonotoneFiberChecks.lean is a name-search scratch
file with a failed check, not a production dependency.

## What this removes, and what it does not

The earlier fixed-number-of-pieces restriction is now removed for bounded
monotone profiles. Both the original profile and any admissible monotone
continuation can be processed by the SAME pointwise rule, without choosing
new palette members or changing the old output prefix.

The bound W is still fixed BEFORE choosing M, and the precision and modulus
threshold depend on W. An inverse-square-root density profile extending
down to a fixed natural cutoff needs an increasing normalized height range
as M grows; this theorem supplies no uniform estimate in that regime.

Moreover, the operators obtained at different moduli are not proved to
agree on old prefixes. Pointwise causality of one operator must not be
confused with compatibility between different operators. No all-target
infinite witness or universal negation of the conjecture has been obtained.
