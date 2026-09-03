# Updated auxiliary search and stale-dependency repair

The conjecture is STILL UNRESOLVED. `Submission/Spec.lean` is unchanged with its original `sorry`; no valid submission was made.

## Updated search

`CheckUpdatedAuxiliaryGoal.lean` imports 305 compiled non-scratch/non-audit auxiliary modules whose source contains no `sorry`, `admit`, or axiom declaration. This adds 13 modules to the earlier 292-module search, including the critical nonlinear detector, composite-error regularity, finite-moment bounds, and strongest almost-prime results.

Both searches failed to close their goals:

* the exact prime-pair infinitude goal at an arbitrary real slope with `1 < alpha` and `Irrational alpha`;
* the negation of the exact universally quantified conjecture.

This is only a failed direct library search, not a mathematical impossibility result. The scratch file intentionally does not compile because its two `exact?` goals remain unsolved. Do not import it into a proof.

## Repaired stale dependencies

The first search exposed obsolete compiled references in `GlobalTwoScaleMean.lean` and `GlobalTwoScaleAllParameters.lean` to an earlier version of `GlobalTwoScaleMinorant.globalLower`.

The two sources have now been migrated to the current `globalMinorant` definition and recompiled:

* `GlobalTwoScaleMean` explicitly defines the damped form and proves `dampedLower_eq_halfDamping_mul` against the current minorant, including its unit convention. Its old half-damping comparison was adjusted to the current definition.
* `GlobalTwoScaleAllParameters` defines its compatibility `globalLower` as the current `globalMinorant`; its pointwise bounds and overlap identity now use the current proved comparisons and the new damped identity.

All printed principal axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. Rerunning the 305-module search then produced only the two expected unsolved-goal errors, without stale-reference errors.

These repairs restore the already-known negative fixed-parameter mean diagnostic. They supply no positive prime-pair lower bound and no irrational counterexample.

## Sources outside the compiled search

Nine further non-scratch sources without placeholder tokens had no compiled `.olean`: `AbelWeight`, `BoundaryCover`, `FiniteCells`, `LiouvilleBlocks`, `PellBarrier`, `QuadraticFloorRecurrence`, `Rotation`, `TranslationRoute`, and `Work`. Their declarations were reviewed. They contain partial summation, finite certificates, coprimality results, conditional criteria, or explicitly limited obstructions—not an unconditional proof or negation of the conjecture. `AbelWeight` is an earlier source in the existing exponential-sum namespace and was not blindly combined with its successor. No additional completed settlement was found.
