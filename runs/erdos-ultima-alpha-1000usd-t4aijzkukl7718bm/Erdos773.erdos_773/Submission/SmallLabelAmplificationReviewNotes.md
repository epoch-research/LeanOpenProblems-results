# Small-label composition review

No new theorem about the original maximum was proved in this review.
Spec.lean is unchanged, with its sole sorry for 0 < epsilon <= 1/3.
The failed original submission has not been resubmitted.

## Arithmetic bookkeeping for one proposed composition

Suppose a root-Sidon construction of exponent alpha is used only to provide
ordinary integer labels below sqrt(q), so that their square-pair sums can
be kept carry-free modulo q. This supplies about q^(alpha/2) labels.
Even IF each label could be packed with q selected indices and IF their
actual positive-difference spectra were compatible, the union would have
about q^(1+alpha/2) roots at height about q^2. Its exponent would be

    alpha_new = 1/2 + alpha/4.

The fixed point is 2/3. This bookkeeping does not assert that the optimistic
packing exists. It shows why this particular use of small integer labels
would not amplify the already established exponent past 2/3.

The case of many larger modular labels is not covered by this calculation.
Such labels can satisfy modular pair matching without being small integer
Sidon roots. Controlling actual cross-fiber differences remains necessary;
the existing partial-fiber equivalence does not supply that control.

## Other constructions rechecked

* Independent coordinatewise matchings need not be reconciled by a blanket
  coherence condition: for a two-block polynomial, the cross term can
  itself enforce the orientation. But the integer square identity does not
  automatically isolate all coordinatewise square sums. Carry-free diagonal
  isolation has a height cost, and unrestricted seed concatenation already
  has verified counterexamples.
* Private-coordinate CRT encodings do not turn equality modulo a prime
  into equality of integer digit-square sums. Using square-sized moduli or
  small digit alphabets incurs a cardinality cost. No improved encoding or
  general impossibility theorem was proved here.
* The existing scalar modular upper inequalities are already known to
  admit near-linear cardinality models simultaneously for all moduli.
  Optimizing those inequalities again cannot by itself give a fixed-power
  upper bound.

These observations do not exclude other composition methods. No actual
square-Sidon exponent above 2/3, near-linear selector, or fixed-power upper
bound was obtained. The strongest actual lower bound remains the separately
proved eventual N^(2/3)/36 bound.
