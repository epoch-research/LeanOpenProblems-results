import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_352 : prefixTransitionCheck 352=true := by decide +kernel
theorem prefix_transition_353 : prefixTransitionCheck 353=true := by decide +kernel
theorem prefix_transition_354 : prefixTransitionCheck 354=true := by decide +kernel
theorem prefix_transition_355 : prefixTransitionCheck 355=true := by decide +kernel
theorem prefix_transition_356 : prefixTransitionCheck 356=true := by decide +kernel
theorem prefix_transition_357 : prefixTransitionCheck 357=true := by decide +kernel
theorem prefix_transition_358 : prefixTransitionCheck 358=true := by decide +kernel
theorem prefix_transition_359 : prefixTransitionCheck 359=true := by decide +kernel
theorem prefix_transition_360 : prefixTransitionCheck 360=true := by decide +kernel
theorem prefix_transition_361 : prefixTransitionCheck 361=true := by decide +kernel
theorem prefix_transition_362 : prefixTransitionCheck 362=true := by decide +kernel
theorem prefix_transition_363 : prefixTransitionCheck 363=true := by decide +kernel
theorem prefix_transition_364 : prefixTransitionCheck 364=true := by decide +kernel
theorem prefix_transition_365 : prefixTransitionCheck 365=true := by decide +kernel
theorem prefix_transition_366 : prefixTransitionCheck 366=true := by decide +kernel
theorem prefix_transition_367 : prefixTransitionCheck 367=true := by decide +kernel

theorem prefix_transitions_22 (i : ℕ) (hi0 : 352 ≤ i) (hi1 : i < 368) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_352
  · exact prefix_transition_353
  · exact prefix_transition_354
  · exact prefix_transition_355
  · exact prefix_transition_356
  · exact prefix_transition_357
  · exact prefix_transition_358
  · exact prefix_transition_359
  · exact prefix_transition_360
  · exact prefix_transition_361
  · exact prefix_transition_362
  · exact prefix_transition_363
  · exact prefix_transition_364
  · exact prefix_transition_365
  · exact prefix_transition_366
  · exact prefix_transition_367

#print axioms prefix_transitions_22
end Erdos7No9Certificate
