# Scaled denominator roughness (verified auxiliary result)

This is not a settlement of Erdős 68. `Submission/Spec.lean` is unchanged,
and still contains the original unproved conjecture.

`Submission/ScaledDenominatorRoughness.lean` compiles and its olean has been
built. The two principal axiom audits list only `propext`, `Classical.choice`,
and `Quot.sound`.

Write

    X_n = (n+1)! * sum_(k=0)^(n-1) 1/((k+2)!-1),

regarded as a rational number in lowest terms.

## Verified conclusions

`scaledSumQ_den_coprime` proves

    gcd(B!, denominator(X_n)) = 1, whenever B! <= n+1.

The proof distributes the factorial multiplier across the rows. For a row
m=k+2 <= B, its denominator m!-1 is positive and at most B! <= n+1,
so it divides (n+1)!. The scaled row is therefore an integer. For a row
m >= B, the denominator m!-1 is coprime to B!, since B! divides m!.
Integer multiplication cannot introduce a new denominator prime, and the
denominator of a finite rational sum divides the product of the denominators.

`scaled_rational_tail_den` proves, for an arbitrary rational q,

    denominator((n+1)!*q-X_n) = denominator(X_n),
    whenever denominator(q) <= n+1.

Here (n+1)!*q is an integer. Subtracting a rational from an integer leaves
its reduced denominator unchanged. The statement does not assume q is the
target series; it applies to any q satisfying the denominator bound.

## What remains missing

If the target series were q, these results would make the scaled rational
tails eventually coprime in denominator to every fixed factorial. Existing
analytic bounds also put these tails strictly between zero and 3/(n+2).
These conditions do not contradict one another. For example, 1/(n!-1)
for n>=2 is positive, tends to zero, and its reduced denominator is coprime
to n!, hence eventually to every fixed factorial. This example is only an
illustration of the insufficient conditions, not a counterexample to the
original conjecture or its exact recurrence.

No new estimate links denominator roughness to infinitely many carry changes.
The outstanding conjecture-equivalent condition remains

    forall N, exists n >= N, carry n != n+1.

No proof or disproof has been submitted.
