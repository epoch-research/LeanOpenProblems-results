# Prime-power block congruences and the remaining nonvanishing gap

This is auxiliary progress, NOT a proof or disproof of Erdos 68.
`Submission/Spec.lean` retains its original statement and `sorry`.

## Verified congruences

`LambertBlockPowerCongruence.lean` concerns the original integer coefficients

    a_n = sum_(d|n, d>=2) n!/(d!)^(n/d).

Its `lowBlockCoeff n J` retains terms with block count n/d <= J.
This is a restriction on block counts, not on row sizes.

For a prime p and J*p <= n < (J+1)*p, the file proves

    a_n = lowBlockCoeff(n,J)  (mod p^J).

There is no assumption J<p. More generally, whenever p^e divides n! and
n < (J+1)*p, the same congruence holds modulo p^e.

Indeed, a discarded term has d|n and n/d>J, hence d<p. Its denominator
(d!)^(n/d) is therefore coprime to p. Multinomial divisibility makes the
quotient exact, and every p-power dividing n! survives in that quotient.
Summing proves the result. The file also proves exact divisibility of the
natural-number remainder and the bound lowBlockCoeff(n,J)<=a_n.

Principal declarations:

* lambertCoeff_modEq_lowBlockCoeff_of_factorial
* lambertCoeff_modEq_lowBlockCoeff
* prime_power_dvd_high_block_remainder

All three printed axiom audits use only propext, Classical.choice, and
Quot.sound. These are original-coefficient results: they do not establish
corresponding congruences for the carried coefficients.

## Boundary-lattice review (informal, not a Lean theorem)

One proposed use was to force additional low-column equations on many
short boundary-clearing vectors. For a window starting at H, shift order
M, dimension D, common boundary denominator C, and weight bound Q, a rough
successive-minimum count guaranteeing D-J independent short vectors asks
for Q^J>C. When H dominates the window lengths, log C is on the scale
H log H, so this asks for log Q at least about H log H/J.

To isolate column j, primes in

    (H+M+D-1)/(j+1) < p <= H/j

can supply modulus p^j after the appropriate factorial normalization.
The resulting product modulus has logarithm on the scale H/j. This is a
genuine improvement over using only p, but the comparison near j=J still
requires a bound of the shape

    2 log Q + (M+D) log H < constant * H/J.

The preceding short-vector estimate does not imply it: it loses a factor
of roughly log H. This is a limitation of these estimates, not an
impossibility theorem about every prime-block construction.

Using the product of all admissible prime-power moduli does not immediately
remove this loss. Predictable factorial factors in the retained column
terms consume part of the apparent larger modulus. A proof must track
those factors and the actual sizes of the normalized column forms; it
cannot compare an unnormalized product modulus with a normalized numerator.
No useful joint-modulus dimension theorem was established in this review.

Other essential qualifications:

* A relation with nonzero weight sum retains an exponential-column value;
  it is not automatically a small rational column form.
* Combining two vectors to cancel the retained coefficient increases
  their weight bounds, roughly quadratically in Q.
* The earlier bounded-window determinant theorem already forces projected
  dependence unconditionally in its small-error range. That dependence is
  not a new consequence of assuming rationality.
* Small-or-zero forms, a nonzero polynomial, and a nonzero weight vector
  are not substitutes for a nonzero value at the target constant.

No complete mathematical argument awaiting formalization was obtained.
Nothing here settles the conjecture, and no proof or disproof has been
submitted.
