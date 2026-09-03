# Post-rough-norm continuation review

The original conjecture remains unresolved. This review produced no new
Lean theorem and no improvement of the actual exponent. Spec.lean was not
changed and has not been submitted as a complete proof.

The completed original-problem result remains eventual M(N)>=N^(2/3).
The sole remaining admission is the branch 0<epsilon<1/3.

## Reviewed routes

- Finite checksums: the verified q=3 and q=5 examples are still finite
  examples, not a uniform q^3-at-height-q^4 construction. No preservation
  argument for concatenation, tensoring, or changing the finite field was
  obtained. Their failures in previously tested formula families do not
  rule out other checksums.
- Sparse translated fibers: modular pair matching is still insufficient
  without separation of actual positive square-difference spectra. Neither
  a capacity estimate on full fibers nor a first-order congruence estimate
  was transferred to arbitrary sparse selections.
- Short translated cubes: the extracted shifts are existential and finite;
  they do not supply Sidonness at all affine parameters. No new argument
  using a large base set and these short shifts was found.
- Stronger digit constraints: increasing moment constraints, imposing
  monotonicity/convexity on digits, and using different polynomial remainder
  constraints were considered informally. No theorem was obtained that
  forces carry disappearance while retaining a near-linear carrier. No
  universal impossibility result for these approaches is asserted.
- Bounded multiplicity: the existing generic counterexamples are already
  three-AP-free and near the square-root ambient scale. A new conversion
  would have to use additional square-specific structure. None was proved.
- Quadratic-shear parabola targets: the affine-target ceiling was not
  silently extended to nonzero quadratic shear. This broader construction
  criterion still lacks enough small root representatives.

No unrestricted fixed-power upper bound on M(N), no actual lower exponent
above 2/3, and no near-linear integer selector was obtained.

The four modules documented in RoughPairNormsResearchNotes.md remain the
latest completed auxiliary work. Their results are not used as a proof of
Sidonness for the extracted rough carriers.

Spec.lean SHA-256 remains:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940

Its sole import is import FormalConjecturesUtil; the original theorem is at
line 17276 and the sole sorry is at line 17287.
