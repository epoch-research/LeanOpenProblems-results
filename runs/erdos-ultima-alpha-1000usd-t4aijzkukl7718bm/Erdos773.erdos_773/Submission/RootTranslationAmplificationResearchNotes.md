# Root-translation amplification review

This continuation did not settle Erdős 773 or improve either main-gap exponent.
No new arithmetic amplification theorem was proved. Spec.lean is unchanged.

The route examined was to enlarge a square-Sidon root set by many translated
copies of its ROOTS, rather than translate its square VALUES. The existing
TranslatedSquareFibers theorem concerns value translations and does not by
itself rule out root-translation amplification.

For candidate roots q*b+a, a collision is exactly

  q^2 (b1^2+b2^2-b3^2-b4^2)
    + 2q (a1*b1+a2*b2-a3*b3-a4*b4)
    + (a1^2+a2^2-a3^2-a4^2) = 0.

Sidonness of either the coarse or the fine square set alone does not imply
that its corresponding coefficient vanishes. Even if modular pair matching
identifies the two residue labels, the two copies may still share ACTUAL
positive square differences. This is exactly the compatibility condition
already isolated in PartialResidueFibers and PartialFiberSelection.

In particular:

* Widely separating coarse square-pair sums can identify the coarse pair,
  but does not dispose of collisions between the two retained fibers.
* Within-fiber Sidonness is insufficient to certify a Sidon union.
* Replacing the cross-difference condition by a modular short-product
  separation condition is only a sufficient restriction; the earlier
  capacity ceilings do not bound arbitrary partial fibers.
* A formal polynomial identity argument cannot be evaluated at a small
  integer base without separately controlling the displayed coefficient
  cancellations. The previously verified specialization counterexamples
  remain relevant.

No assertion that every root-translation strategy is impossible is made.
The review found no subpower-loss selector for the cross-differences.
The previously proved equivalence with subpower-loss amplification therefore
remains conditional, not a proof of the original conjecture.
