# Multiplicative-diagonal bounds — no settlement

Spec.lean remains unchanged with its original sorry. The conjecture has not
been proved or disproved. No incomplete proof was submitted.

## New verified files

### FloorDiagonalCount.lean

Namespace Erdos972FloorDiagonalCount; imports RationalRotationCount.
All principal declarations compile with only propext, Classical.choice,
and Quot.sound in their audits.

For alpha>=0, a,q natural, q>0, gcd(a,q)=1, assume

    |alpha-a/q| * N <= 1,    N <= q^2.

`diagonal_factor_le` proves that if m>0, m*p<=N, and

    k*p = floor(alpha*m*p),

then p<=2q. Primality is not needed.

`diagonalRows alpha N p` consists of positive m<=N/p with
fractionalPart(alpha*m)<1/p.

`floor_diagonal_iff` proves the exact equivalence, for p>0,

    k*p = floor(alpha*m*p)
      iff k=floor(alpha*m) and fractionalPart(alpha*m)<1/p.

`diagonal_row_bound` gives

    card(diagonalRows alpha N p)
      <= 10N/p^2 + (2N/q+5q)/p + 1.

The interval width 1/p is retained in the rational-rotation lattice bound;
using the older coarse O(p*q) discrepancy here would lose too much.

`diagonal_count_bound`, for V>0, gives

    sum_{V<p<=N} card(diagonalRows alpha N p)
      <= 10N/V + (2N/q+5q)*(1+log(2q)) + 2q.

This bounds all natural factors p, not just primes. The proof uses the
p<=2q restriction before summing the row errors. It retains both the
reciprocal-square main term and the harmonic denominator error.

`weighted_diagonal_bound` multiplies this estimate by any proved uniform
bound B on the absolute values of real weights on the actual rows.

### VaughanDiagonalBound.lean

Namespace Erdos972VaughanDiagonalBound. Compiles and audits with only the
three allowed axioms.

`divisorCoeff_abs_le` proves |a_U(n)|<=U+1 uniformly in n, where a_U is the
actual coefficient (mu_{>U} * zeta).

`vaughanDiagonal alpha N U V` is the reindexed equal-Mangoldt-factor sum

    sum_{V<p<=N} sum_{m in diagonalRows alpha N p}
      a_U(m) * a_U(floor(alpha*m)) * Lambda(p)^2.

The exact floor equivalence above identifies the multiplier and the row
condition. No identity decomposing the full fourFactorRemainder into this
sum plus a newly defined off-diagonal sum has yet been added.

`vaughan_diagonal_bound` bounds its absolute value by

    (U+1)^2 * log(N)^2 *
      [10N/V + (2N/q+5q)*(1+log(2q)) + 2q].

## What this does not prove

The finite bounds are unconditional under the explicit approximation and
size hypotheses. They are not a signed off-diagonal estimate.

In particular, the factor (U+1)^2 means the first term is not automatically
o(N) at the existing symmetric cutoffs U=V. Asymmetric choices V much
larger than U^2*log(N)^2, with q around N^(2/3), are suggested by the bound,
but no new common-scale asymptotic theorem or altered four-factor reduction
has been formalized here. Do not claim that the existing centered remainder
has thereby become nonnegative or negligible.

The essential task remains a genuine prime-pair lower bound, a strict
signed four-factor gap, or an actual irrational counterexample.
