# Sharper raw-operator bounds (verified auxiliary progress)

This is NOT a settlement of Erdos 68. Spec.lean is unchanged and still has
its original sorry. No proof or disproof of that conjecture has been obtained.

## Files and verification

Both new files compile without warnings and have built oleans:

* LambertSharperOperatorBounds.lean
* FactorialGeometricProductBound.lean

All printed principal axiom audits contain only propext, Classical.choice,
and Quot.sound. No external computation is used in these Lean proofs.

Write lambda_d=(d!)^(1/d), and let

    Q_K(E)=product_(k=2)^(K+1) (k! E^k-1).

Here K counts the cancelled rows. This is the indexing used in the Lean
files; the separate lattice experiments cancel rows 2 through K instead.

## Exact weighted operator bound

The first file replaces the stepwise factor 2 by the exact factor

    1 + k!/x^k.

If |r_n|<=C/x^n and x>0, then

    |Q_K(E)r_n| <= C/x^n * product_(k=2)^(K+1)(1+k!/x^k).

The generic list version is rawApply_weighted_bound. Applying it to an
uncancelled geometric row gives rawApply_row_weighted_bound, with C=2 and
x=lambda_d. This estimate itself does not require each shift index to be
less than d.

The file also uses Mathlib's Stirling lower bound to prove

    d/exp(1) <= lambda_d,
    d/3 <= lambda_d.

Already this replaces the old full-tail bound

    2^(K+1)/(K+1)^(floor(n/2)-1)

by

    2^(K+1)*3^n/(K+1)^(n-1),       n>=2.

## Uniform product bound

The second file proves, for d>=6,

    sum_(k=0)^d k!/lambda_d^k <= 12.

The constant is deliberately coarse and independent of d. The proof is
elementary apart from the preceding Stirling lower bound:

1. Bernoulli's inequality and induction give

       k! <= 2*(k/2)^k  for all k,
       d! <= (d/2)^d    for d>=6.

2. If 2k<=d, the lower rate bound implies

       k!/lambda_d^k <= 2*(3/4)^k.

3. Pairing an ascending factorial's factors proves

       ((k+1)*d)^(d-k) <= (d!/k!)^2.

   Together with lambda_d<=d/2, this gives, when d<=2k and k<=d,

       k!/lambda_d^k <= (3/4)^(d-k).

4. Bound every term by the sum of the two geometric majorants and sum.
   Their total is at most 2*4+4=12.

Since 1+t<=exp(t), the theorem weightedProduct_range_le_exp_twelve proves

    product_(k=2)^(K+1)(1+k!/lambda_d^k) <= exp(12)

whenever d>=6 and K+1<=d. Thus the operator prefactor need not grow like 2^K.

## Full infinite-tail bound

The main theorem range_operator_uniform_bound verifies, for K>=4 and n>=2,

    |Q_K(E)(alpha-S_n)|
       <= 2*exp(12)*exp(1)^n/(K+1)^(n-1).

All omitted rows are retained in the estimate. The proof uses the already
verified row decomposition, cancellation of rows 2 through K+1, norm bounds
for the infinite sum, and the elementary p-series tail comparison.

This improves both the power of the decay and the dependence on K in the
prefactor. It does NOT prove positivity, nonvanishing, independence of
cleared coefficient pairs, or a useful bound on the final projected lattice
minima. The finite lattice tests in LambertBoundaryGeometryNotes.md remain
finite tests. No original-conjecture theorem has been submitted.
