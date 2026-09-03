import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_336 : prefixTransitionCheck 336=true := by decide +kernel
theorem prefix_transition_337 : prefixTransitionCheck 337=true := by decide +kernel
theorem prefix_transition_338 : prefixTransitionCheck 338=true := by decide +kernel
theorem prefix_transition_339 : prefixTransitionCheck 339=true := by decide +kernel
theorem prefix_transition_340 : prefixTransitionCheck 340=true := by decide +kernel
theorem prefix_transition_341 : prefixTransitionCheck 341=true := by decide +kernel
theorem prefix_transition_342 : prefixTransitionCheck 342=true := by decide +kernel
theorem prefix_transition_343 : prefixTransitionCheck 343=true := by decide +kernel
theorem prefix_transition_344 : prefixTransitionCheck 344=true := by decide +kernel
theorem prefix_transition_345 : prefixTransitionCheck 345=true := by decide +kernel
theorem prefix_transition_346 : prefixTransitionCheck 346=true := by decide +kernel
theorem prefix_transition_347 : prefixTransitionCheck 347=true := by decide +kernel
theorem prefix_transition_348 : prefixTransitionCheck 348=true := by decide +kernel
theorem prefix_transition_349 : prefixTransitionCheck 349=true := by decide +kernel
theorem prefix_transition_350 : prefixTransitionCheck 350=true := by decide +kernel
theorem prefix_transition_351 : prefixTransitionCheck 351=true := by decide +kernel

theorem prefix_transitions_21 (i : ℕ) (hi0 : 336 ≤ i) (hi1 : i < 352) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_336
  · exact prefix_transition_337
  · exact prefix_transition_338
  · exact prefix_transition_339
  · exact prefix_transition_340
  · exact prefix_transition_341
  · exact prefix_transition_342
  · exact prefix_transition_343
  · exact prefix_transition_344
  · exact prefix_transition_345
  · exact prefix_transition_346
  · exact prefix_transition_347
  · exact prefix_transition_348
  · exact prefix_transition_349
  · exact prefix_transition_350
  · exact prefix_transition_351

#print axioms prefix_transitions_21
end Erdos7No9Certificate
