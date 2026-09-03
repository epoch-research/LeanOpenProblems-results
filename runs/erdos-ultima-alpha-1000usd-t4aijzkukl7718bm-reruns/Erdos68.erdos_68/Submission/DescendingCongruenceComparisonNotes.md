# Descending congruences with positive quadratic tails: rational comparison

Verified auxiliary progress, NOT a proof or disproof of Erdos 68.
Spec.lean is unchanged and still contains its original sorry. No complete
informal proof or disproof was found or submitted in this continuation.

`Submission/DescendingCongruenceComparison.lean` compiles without warnings
and has a built olean. Its three printed principal axiom audits list only
propext, Classical.choice, and Quot.sound. It has no proof holes.

## Strengthening the previously known limitation

The previous LambertCongruenceComparison preserves every coefficient-to-one
congruence, but does not provide polynomial tails. The simpler existing
QuadraticTailComparison in fact preserves the entire NEW descending-factorial
congruence family while retaining positive strict quadratic tails.

Recall its exact integer sequences:

    t_n = n-3                  for even n,
    t_n = n*(n-4)-1            for odd n,
    c_n = 0                    for n<5,
    c_n = n*t_(n-1)-t_n        for n>=5.

For odd n>=5, c_n=1. For even n>=6,

    c_n = (n-1)*(n*(n-5)-2)+1.

The earlier file proves the sum of c_n/n! is 1/24 and its actual scaled
factorial tail at n>=4 is t_n.

The new file verifies:

* c_n>0 for every n>=5; all earlier coefficients are nonnegative;
* c_p=1 for every prime p>=5;
* for n>=5 and j<minFac(n),

      (n-1).descFactorial(j) divides c_n-1;

* in particular the maximal modulus with j=minFac(n)-1 divides c_n-1;
* minFac(n)! divides c_n-1 for every n>=5;
* 0<T_n<n^2 for every n>=4;
* T_n<n at every even n>=4;
* the exact rational sum remains 1/24.

The congruence proof is elementary. At odd indices c_n-1 is zero, so every
modulus divides it. At an even index minFac(n)=2, hence j is zero or one;
the required descending modulus is respectively one or n-1. For the
factorial congruence, n*(n-5)-2 is even.

Principal declarations:

* descending_congruence
* maximal_descending_congruence
* minFac_factorial_congruence
* coeff_pos
* strict_tail_bounds
* even_tail_bound
* comparison_properties

## Precise scope

This is a DIFFERENT sequence, not the original Lambert coefficients and
not a new carried representation of the original sum. It cannot be used
as an erdos_68.disproof. It shows that transferring all the new descending
congruences into a representation with merely quadratic tails would still
be insufficient, even with the displayed even-index linear bound.

The distinction between EVEN and NONPRIME indices is essential: at odd
composite indices this comparison has quadratic, not linear, tails. Thus
it does not refute a criterion combining these congruences with the sharper
linear tail bound at EVERY composite index of the actual target carry.
No such congruence inheritance or infinite occurrence theorem has been
proved for that carry.

## Other review in this continuation

The existing positive-kernel examples still supply only fixed small integral
forms. Their ordinary powers do not stay in the telescoping class; no new
closure operation or integral-boundary height estimate was found.

The simultaneous-boundary route still needs a detected phase that is also
integral. For an EXACT polynomial factor, a block of zero outputs propagates
to the quotient operator algebraically without an integrality-transfer claim.
That observation alone does not supply a detector for near-factors or a
compatible counting bound; small nondivisible row responses remain possible.
No new multi-row detection theorem or proof of irrationality resulted.

All compilation and axiom checks have completed. Nothing is running or
pending. The original conjecture remains unproved and undisproved here.
