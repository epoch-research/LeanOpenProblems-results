# Gaussian-factor selector review after the binary-polynomial theorem

The original conjecture remains UNSETTLED. This continuation produced no new
Lean theorem, no integer exponent improvement, and no disproof. Spec.lean
was not edited, and no incomplete proof was submitted.

The review targeted the following possible bridge rather than another
formal-polynomial specialization claim:

* Equal square sums admit the already verified small primitive Gaussian
  factor parametrization. For a fixed factor of norm q, partners lie in one
  residue class modulo q. The resulting harmonic bound still has quadratic
  collision scale. Removing only small factors does not establish the
  near-linear low-collision target.
* Full residue fibers are individually Sidon at the short unit-fiber scale,
  but their union requires actual positive-difference compatibility.
  FullFiberOverlap gives real overlap witnesses, not just modular aliases.
  Its weighted independent-selection certificate cannot improve the
  two-thirds exponent. No application of that ceiling to arbitrary partial
  fibers is justified.
* A partial-fiber selector with sufficiently large mass and small overlap
  cost would be a valid route. No such selector was constructed. The proved
  sum/difference capacities remain capacities greater than one, not a
  subpower-loss rounding theorem.

Narrow-interval, large-factor, and multiscale variants were reconsidered
mathematically, but none yielded a count or selection lemma that closes this
gap. These observations are not claimed as additional impossibility theorems.

An external-reference check again failed: curl could not resolve
www.erdosproblems.com. No result was obtained from that request.

The preceding BinaryPolynomialSidon module remains clean and built. It is
strictly formal and includes a verified evaluation failure; it cannot be
used to replace the missing integer argument.

Spec.lean remains at SHA-256
f019ff3791c89bbea24fd9b031eb92f7b676baa4b1ff9cebe9f2356121aa6ff0.
Its original declaration is at line 2027 and its sole admission is at 2035.
