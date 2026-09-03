# Quantitative lower-bound progress

This does NOT settle Erdős 773. The main file `Spec.lean` now has 1787 lines,
with its one admission at line 1785. The unproved range is still
0 < epsilon <= 1/3. Its sole import and exact conjecture statement are unchanged.

## New verified result, consolidated into Spec.lean

For all sufficiently large N,

    maxSidonSubsetCard({1^2,...,N^2})
      >= N / (8 * (N * (1 + log(2*N)))^(1/3))
       = N^(2/3) / (8 * (1 + log(2*N))^(1/3)).

The theorem is `Erdos773.square_sidon_logarithmic_lower`.
This sharpens the earlier N^(2/3-o(1)) lower bound by giving a logarithmic loss.
It does not cover epsilon=1/3, much less smaller positive epsilon.

## Proof structure

`AverageCollisionBound.lean` proves a general average multiplicative-energy bound.
Any positive solution a*b=c*d with all variables <=M has a parametrization

    a=r*g, c=s*g, b=s*h, d=r*h,
    gcd(r,s)=1,
    g,h <= M/max(r,s).

Discarding the coprimality condition gives an upper bound by

    sum_{r,s<=M} floor(M/max(r,s))^2
      <= 2 sum_{r<=M} r*floor(M/r)^2
      <= 2 M^2 H_M
      <= 2 M^2 (1+log M).

Square-sum collisions inject into these product equalities using
(a-b)(a+b)=(d-c)(d+c), with M=2N. Consequently

    card(squareCollisions N) <= 8 N^2 (1+log(2N)).

`LogarithmicLowerBound.lean` combines this estimate with the existing alteration
argument. Put L=1+log(2N), R=(N*L)^(1/3), and select each root with probability
p=1/(4R). The existing AP bound with delta=1/4 gives APcount <= C*N^(3/2).
Eventually C<=N^(1/6), so APcount<=N*R^2. The expected deletion costs are at most
p*N/16 for three-point obstructions and p*N/8 for four-point obstructions.
The remaining size is at least p*N/2=N/(8R).

## Verification

Both scratch modules compile. Their required lemmas were copied into Spec.lean,
without adding imports. The consolidated Spec.lean compiles, with the expected
warning for the still-admitted main conjecture and harmless linter warnings.

`LogLowerAudit.lean` imports the newly built Spec module and audits:
- AverageCollision.productQuads_log_bound
- AverageCollision.squareCollisions_log_bound
- square_sidon_logarithmic_lower
- conjecture_for_epsilon_gt_third
- square_sidon_primorial_upper

Every audited result depends exactly on propext, Classical.choice, and Quot.sound.
The unfinished main conjecture is NOT among the clean audited results.

Backup before consolidation: `SpecPrimorialUpperBackup.lean`.
No submit_proof call was made; the incomplete main file is not a valid settlement.

## Research notes

No stronger construction was found in Mathlib. Standard finite-field Sidon
constructions do not directly give many integer squares: a large Sidon set in
[1,N^2] may have very few squares. Preserving the small-root condition during
lifting is the unresolved issue, not just constructing an abstract Sidon set.
A Pisot/trace encoding was considered but gave no usable bound: conjugate-size
and discriminant costs prevent the naive trace argument from preserving the
needed density. These observations are limitations of the attempted methods,
not impossibility theorems about the original problem.

An additional network attempt using DNS-over-HTTPS at a known IP timed out.
No external literature or updated problem status was retrieved.
