# Distinct digit permutations still admit carries

This is NOT a settlement of Erdős 773. No positive main-gap construction or
new exponent was obtained. `Spec.lean` is unchanged and still admitted for
0 < epsilon <= 1/3. No proof submission has been made.

## Verified concrete result

`DistinctDigitCarryObstacle.lean` proves
`Erdos773.DistinctDigitCarry.distinct_digit_conditions_do_not_suffice`.
It supplies four 28-digit words at the prime base B=372689, using parameters
u=615 and v=606. For each word:

* The leading digit is 1 and the constant digit is exactly 3.
* Every lower digit is divisible by 3.
* Every digit is positive, and twice every digit is less than B.
* All 28 digits are distinct.
* The four complete digit histograms agree.
* The common digit sum is 111799, less than B.

The represented roots are pairwise coprime. Nevertheless their squares have
a nontrivial equal sum, and hence do not form a Sidon set.

All of these claims, including primality and pairwise coprimality, are checked
in Lean. The finite certificates use ordinary trusted computation
(`decide +kernel`), not native_decide. All four printed axiom audits contain
only propext, Classical.choice, and Quot.sound. Log:
`/tmp/distinct-digit-carry.log`.

## Exact symbolic identity

The file defines the four words for arbitrary u,v, evaluates them at B, and
proves that the square-sum difference equals

    120 B^35 (B-1)^2 (B+1)^2 (uv-B-1)
        (B^6+B^5+B^4+B^3+B^2+B+1).

Thus evaluation collides whenever B+1=uv. The common digit sum and squared
norm are also proved symbolically:

    168u + 9v + 3025,
    6858u^2 + 35v^2 + 1470v + 800101.

Only the concrete parameter choice above packages all the distinctness,
prime-base, and coprimality conditions. Do not claim that pairwise
coprimality has been proved uniformly for the symbolic family.

## Construction

The earlier carry construction required two equal endpoint digits. The new
construction replaces its short conjugate-palindromic pattern with the two
permutations

    x = [3,30,12,60,42,21],
    y = [3,60,42,30,12,21].

Both have distinct entries and the same, distinct endpoints. Their adjacent
sums, including the endpoints, are

    x' = [3,33,42,72,102,63,21],
    y' = [3,63,102,72,42,33,21].

The multiset of pairs (x'_j,y'_j) is invariant under swapping coordinates.
Take q with coefficients (x_j+y_j)/2 + i*(y_j-x_j)/2, and put

    r = 1 + (4+i) X^7 + (4-i) X^14,
    Q = X^6 + u*q,  R = X^21 + v*r.

Compare the real and imaginary parts of (1+i)QR and (1+i)conj(Q)R.
Replacing uv by B+1 gives the displayed words and their equal histograms.
The all-distinct digit check is now possible because x has distinct
endpoints, unlike the previous 20-digit construction.

Exploratory scripts: `/tmp/distinct_carry_candidate.py` and its log.
The final Lean proof does not depend on Sympy or search output.

## Scope

This refutes a blanket sufficient criterion based on these digit conditions.
It does not show that every histogram or permutation class is bad, and it
does not exclude a special choice of a larger or full alphabet. The single
finite counterexample is not a counterexample to the original asymptotic
conjecture. No new material was consolidated into `Spec.lean`.
