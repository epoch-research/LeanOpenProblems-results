import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_432 : prefixTransitionCheck 432=true := by decide +kernel
theorem prefix_transition_433 : prefixTransitionCheck 433=true := by decide +kernel
theorem prefix_transition_434 : prefixTransitionCheck 434=true := by decide +kernel
theorem prefix_transition_435 : prefixTransitionCheck 435=true := by decide +kernel
theorem prefix_transition_436 : prefixTransitionCheck 436=true := by decide +kernel
theorem prefix_transition_437 : prefixTransitionCheck 437=true := by decide +kernel
theorem prefix_transition_438 : prefixTransitionCheck 438=true := by decide +kernel
theorem prefix_transition_439 : prefixTransitionCheck 439=true := by decide +kernel
theorem prefix_transition_440 : prefixTransitionCheck 440=true := by decide +kernel
theorem prefix_transition_441 : prefixTransitionCheck 441=true := by decide +kernel
theorem prefix_transition_442 : prefixTransitionCheck 442=true := by decide +kernel
theorem prefix_transition_443 : prefixTransitionCheck 443=true := by decide +kernel
theorem prefix_transition_444 : prefixTransitionCheck 444=true := by decide +kernel
theorem prefix_transition_445 : prefixTransitionCheck 445=true := by decide +kernel
theorem prefix_transition_446 : prefixTransitionCheck 446=true := by decide +kernel
theorem prefix_transition_447 : prefixTransitionCheck 447=true := by decide +kernel

theorem prefix_transitions_27 (i : ℕ) (hi0 : 432 ≤ i) (hi1 : i < 448) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_432
  · exact prefix_transition_433
  · exact prefix_transition_434
  · exact prefix_transition_435
  · exact prefix_transition_436
  · exact prefix_transition_437
  · exact prefix_transition_438
  · exact prefix_transition_439
  · exact prefix_transition_440
  · exact prefix_transition_441
  · exact prefix_transition_442
  · exact prefix_transition_443
  · exact prefix_transition_444
  · exact prefix_transition_445
  · exact prefix_transition_446
  · exact prefix_transition_447

#print axioms prefix_transitions_27
end Erdos7No9Certificate
