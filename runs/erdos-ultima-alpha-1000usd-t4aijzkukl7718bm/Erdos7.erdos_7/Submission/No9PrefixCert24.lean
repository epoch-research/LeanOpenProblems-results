import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_384 : prefixTransitionCheck 384=true := by decide +kernel
theorem prefix_transition_385 : prefixTransitionCheck 385=true := by decide +kernel
theorem prefix_transition_386 : prefixTransitionCheck 386=true := by decide +kernel
theorem prefix_transition_387 : prefixTransitionCheck 387=true := by decide +kernel
theorem prefix_transition_388 : prefixTransitionCheck 388=true := by decide +kernel
theorem prefix_transition_389 : prefixTransitionCheck 389=true := by decide +kernel
theorem prefix_transition_390 : prefixTransitionCheck 390=true := by decide +kernel
theorem prefix_transition_391 : prefixTransitionCheck 391=true := by decide +kernel
theorem prefix_transition_392 : prefixTransitionCheck 392=true := by decide +kernel
theorem prefix_transition_393 : prefixTransitionCheck 393=true := by decide +kernel
theorem prefix_transition_394 : prefixTransitionCheck 394=true := by decide +kernel
theorem prefix_transition_395 : prefixTransitionCheck 395=true := by decide +kernel
theorem prefix_transition_396 : prefixTransitionCheck 396=true := by decide +kernel
theorem prefix_transition_397 : prefixTransitionCheck 397=true := by decide +kernel
theorem prefix_transition_398 : prefixTransitionCheck 398=true := by decide +kernel
theorem prefix_transition_399 : prefixTransitionCheck 399=true := by decide +kernel

theorem prefix_transitions_24 (i : ℕ) (hi0 : 384 ≤ i) (hi1 : i < 400) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_384
  · exact prefix_transition_385
  · exact prefix_transition_386
  · exact prefix_transition_387
  · exact prefix_transition_388
  · exact prefix_transition_389
  · exact prefix_transition_390
  · exact prefix_transition_391
  · exact prefix_transition_392
  · exact prefix_transition_393
  · exact prefix_transition_394
  · exact prefix_transition_395
  · exact prefix_transition_396
  · exact prefix_transition_397
  · exact prefix_transition_398
  · exact prefix_transition_399

#print axioms prefix_transitions_24
end Erdos7No9Certificate
