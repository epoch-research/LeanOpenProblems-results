# Status of the exploratory finite analogue

The original natural-number theorem in `Spec.lean` is **not proved or disproved**.
It still contains its original `sorry`. None of the files described below is a
submission settling that theorem.

New checked files:

* `CharacterNormExplore.lean`: quadratic characters commute with finite-field
  norms; they are preserved in odd-degree extensions. If L/K is quadratic,
  nu is nonsquare in K, and alpha^2 = nu, then
  chi_L(alpha+x) = chi_K(x^2-nu).
* `CosetExplore.lean`: the affine coset alpha+K has character-fiber L1 norm E
  satisfying E^2 <= 3|K|^3. Combining the graph construction and origin repair,
  any tower K < L < F with [L:K]=2 and [F:L] odd >=3 admits a subset A of F x F
  with, at every target z,

      |pairCount(A,A,z) - |K|^2| <= E + 2|K| + 6.

  This includes the origin, and contains no assumptions about the existence
  of auxiliary repair sets or a prescribed character pattern.
* `FiniteAnalogueExplore.lean`: the tower is instantiated with Mathlib finite
  extensions. For any finite odd-characteristic K and odd d>=3, there exists
  a finite field F of cardinality |K|^(2d) and a set A as above.

All these files compile. The final existence theorem
`Erdos66FiniteAnalogue.exists_flat_finite_field` was axiom-checked and depends
only on propext, Classical.choice, and Quot.sound.

The remaining gap is substantial: these are finite elementary-abelian additive
 groups, not cyclic groups or intervals of integers. No proved transference
argument controls integer carries, truncation, or interactions between scales.
In particular the exact compactness reduction in `CompactnessExplore.lean`
requires a single nonzero c and a single threshold function N chosen before
all finite prefix lengths; the finite-field results do not supply that.
