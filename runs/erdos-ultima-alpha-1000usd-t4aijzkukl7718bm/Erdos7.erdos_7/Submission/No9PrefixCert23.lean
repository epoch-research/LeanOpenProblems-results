import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_368 : prefixTransitionCheck 368=true := by decide +kernel
theorem prefix_transition_369 : prefixTransitionCheck 369=true := by decide +kernel
theorem prefix_transition_370 : prefixTransitionCheck 370=true := by decide +kernel
theorem prefix_transition_371 : prefixTransitionCheck 371=true := by decide +kernel
theorem prefix_transition_372 : prefixTransitionCheck 372=true := by decide +kernel
theorem prefix_transition_373 : prefixTransitionCheck 373=true := by decide +kernel
theorem prefix_transition_374 : prefixTransitionCheck 374=true := by decide +kernel
theorem prefix_transition_375 : prefixTransitionCheck 375=true := by decide +kernel
theorem prefix_transition_376 : prefixTransitionCheck 376=true := by decide +kernel
theorem prefix_transition_377 : prefixTransitionCheck 377=true := by decide +kernel
theorem prefix_transition_378 : prefixTransitionCheck 378=true := by decide +kernel
theorem prefix_transition_379 : prefixTransitionCheck 379=true := by decide +kernel
theorem prefix_transition_380 : prefixTransitionCheck 380=true := by decide +kernel
theorem prefix_transition_381 : prefixTransitionCheck 381=true := by decide +kernel
theorem prefix_transition_382 : prefixTransitionCheck 382=true := by decide +kernel
theorem prefix_transition_383 : prefixTransitionCheck 383=true := by decide +kernel

theorem prefix_transitions_23 (i : ℕ) (hi0 : 368 ≤ i) (hi1 : i < 384) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_368
  · exact prefix_transition_369
  · exact prefix_transition_370
  · exact prefix_transition_371
  · exact prefix_transition_372
  · exact prefix_transition_373
  · exact prefix_transition_374
  · exact prefix_transition_375
  · exact prefix_transition_376
  · exact prefix_transition_377
  · exact prefix_transition_378
  · exact prefix_transition_379
  · exact prefix_transition_380
  · exact prefix_transition_381
  · exact prefix_transition_382
  · exact prefix_transition_383

#print axioms prefix_transitions_23
end Erdos7No9Certificate
