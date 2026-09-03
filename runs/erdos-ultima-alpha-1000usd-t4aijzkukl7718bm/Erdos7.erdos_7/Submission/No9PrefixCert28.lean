import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_448 : prefixTransitionCheck 448=true := by decide +kernel
theorem prefix_transition_449 : prefixTransitionCheck 449=true := by decide +kernel
theorem prefix_transition_450 : prefixTransitionCheck 450=true := by decide +kernel
theorem prefix_transition_451 : prefixTransitionCheck 451=true := by decide +kernel
theorem prefix_transition_452 : prefixTransitionCheck 452=true := by decide +kernel
theorem prefix_transition_453 : prefixTransitionCheck 453=true := by decide +kernel
theorem prefix_transition_454 : prefixTransitionCheck 454=true := by decide +kernel
theorem prefix_transition_455 : prefixTransitionCheck 455=true := by decide +kernel
theorem prefix_transition_456 : prefixTransitionCheck 456=true := by decide +kernel
theorem prefix_transition_457 : prefixTransitionCheck 457=true := by decide +kernel
theorem prefix_transition_458 : prefixTransitionCheck 458=true := by decide +kernel
theorem prefix_transition_459 : prefixTransitionCheck 459=true := by decide +kernel
theorem prefix_transition_460 : prefixTransitionCheck 460=true := by decide +kernel
theorem prefix_transition_461 : prefixTransitionCheck 461=true := by decide +kernel
theorem prefix_transition_462 : prefixTransitionCheck 462=true := by decide +kernel
theorem prefix_transition_463 : prefixTransitionCheck 463=true := by decide +kernel

theorem prefix_transitions_28 (i : ℕ) (hi0 : 448 ≤ i) (hi1 : i < 464) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_448
  · exact prefix_transition_449
  · exact prefix_transition_450
  · exact prefix_transition_451
  · exact prefix_transition_452
  · exact prefix_transition_453
  · exact prefix_transition_454
  · exact prefix_transition_455
  · exact prefix_transition_456
  · exact prefix_transition_457
  · exact prefix_transition_458
  · exact prefix_transition_459
  · exact prefix_transition_460
  · exact prefix_transition_461
  · exact prefix_transition_462
  · exact prefix_transition_463

#print axioms prefix_transitions_28
end Erdos7No9Certificate
