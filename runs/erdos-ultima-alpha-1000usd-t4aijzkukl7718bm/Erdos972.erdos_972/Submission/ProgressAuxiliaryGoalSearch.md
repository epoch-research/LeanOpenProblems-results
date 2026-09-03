# Whole-auxiliary goal search — no settlement

`Submission/Spec.lean` remains unchanged with its original `sorry`. No proof
or disproof was obtained, and no incomplete proof was submitted.

## New local audit

* Found 301 compiled auxiliary `.olean` files.
* Constructed `Submission/CheckAllAuxiliaryGoal.lean` importing 292 compiled
  non-scratch/non-audit auxiliary modules whose source files contained no
  `sorry`, `admit`, or axiom declaration.
* No auxiliary source directly imports `Submission.Spec`; the original
  `erdos_972` name occurs only in `Spec.lean`.
* Ran `exact?` on the exact pointwise goal with arbitrary real alpha,
  `1 < alpha`, and `Irrational alpha`, using the explicit prime-pair set.
  The search failed to close the goal.
* Reviewed the nearby infinitude conclusions. The pointwise criteria still
  carry arithmetic hypotheses; the unconditional infinitude results are
  generic, metric, or existential in the slope.

This is not a mathematical impossibility result about combining the
auxiliary lemmas. It records only that the expanded automated search found
no immediate completed proof. The new `CheckAllAuxiliaryGoal.lean` is an
intentionally failing exploratory scratch file, not a submission or a
completed proof file.
