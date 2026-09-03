# Local-digit continuation review

The conjecture is still UNSETTLED. No Lean source was changed in this
continuation, and no incomplete proof was submitted. Spec.lean retains
its sole admission at line 17287, for 0 < epsilon < 1/3. The completed
unconditional endpoint remains eventual M(N) >= N^(2/3).

## Local digit restrictions

The approach reconsidered was to impose a small number of digit statistics
inside each long aligned block. The entropy cost can be small relative to
the full word length, but that fact supplies no Sidon theorem. No argument
was obtained that controls all carries in a square-sum identity from such
local restrictions.

Important qualifications retained:

* Gaussian-Eisenstein formal Sidonness is not integer Sidonness.
* The existing aligned-block repetition counterexample loses GLOBAL
  Eisenstein divisibility at its interior block-leading digits. It was not
  used as a counterexample to a criterion retaining that global condition.
* Conversely, the absence of a counterexample to a combined criterion is
  not a proof of the criterion.
* Adding or repeating a COMMON digit block does not generally preserve a
  nontrivial square-sum collision: a common additive change introduces a
  term proportional to the difference of the two root-pair sums.
* Common multiplicative padding preserves an evaluated collision, but its
  canonical carries must still be checked before claiming preservation of
  digit divisibility, a fixed leading digit, or local histogram constraints.

No carry-safe near-linear class, useful low-collision estimate, or improved
actual Sidon exponent was obtained. The earlier exact seed tensor counts
remain only finite exploratory counts, not an asymptotic recurrence.

## File state

Spec.lean's conjecture, import, and proof text are unchanged. SHA-256:

    257d2e55d464b8ea5a35ca7f1257dc2f59e682772c2f52fa771ee4bfdf9b8940

The latest completed auxiliary theorems remain the full-interval packing
and rounded FULL-block ceiling. They do not bound arbitrary sparse
selections. No unrestricted fixed-power upper bound was found.
