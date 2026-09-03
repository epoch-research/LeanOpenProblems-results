# Main-gap continuation review

The original conjecture remains unsettled. This continuation changed no Lean
source. Spec.lean retains its sole admission at line 17287, in the range
0 < epsilon < 1/3. The proved endpoint remains eventual M(N) >= N^(2/3).
No incomplete proof was submitted.

## Partial fibers

The existing modular matching criterion still requires actual disjointness
of the positive-difference spectra of the chosen partial fibers. Modular
aliases alone do not establish actual collisions, and avoiding the endpoints
in the full-fiber overlap constructions remains possible for partial fibers.
No compatible near-linear selector or favorable overlap-cost estimate was
obtained. The full-fiber ceilings were not applied to arbitrary subsets.

## A block amplification check

At target root height M^2, placing a full block of M roots near each of
M^alpha coarse labels would formally have the attractive cardinality
M^(1+alpha). However, writing roots as M*a+u gives the exact equation

  M^2*(a^2+b^2-c^2-d^2)
    +2*M*(a*u+b*v-c*w-d*z)
    +(u^2+v^2-w^2-z^2)=0.

Coarse integer square-Sidonness excludes only a zero leading discrepancy
with nonmatching labels. It does not exclude cancellation of a NONZERO
leading discrepancy by the cross term. For labels and indices of order M,
the cross term can have order M^3, while the least nonzero leading term is
only of order M^2. Thus the putative exponent map (1+alpha)/2 is not proved.
No near-linear carry-aware choice of the indices was found here.

## Other checks

* Quadratic-shear modular targets still require a proved count of small
  integer representatives; the existing finite transfer theorem supplies
  no such count by itself.
* Formal Gaussian polynomial Sidonness remains distinct from integer
  specialization. Neither fixed statistics nor the verified single-swap
  result controls general permutation collisions.
* The known stretched-exponential/subpower-loss upper bounds remain
  compatible with the original quantifiers. Their losses cannot be
  replaced by a fixed epsilon without a new argument.
* External reference access was unavailable: DNS resolution for
  www.erdosproblems.com failed again.

The preceding AllowedAlphabetSwapRigidity module remains fully verified,
including actual transposition formulas and its five clean axiom audits.
No additional unconditional theorem about the original maximum was obtained
in this review.
