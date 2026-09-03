import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_496 : prefixTransitionCheck 496=true := by decide +kernel
theorem prefix_transition_497 : prefixTransitionCheck 497=true := by decide +kernel
theorem prefix_transition_498 : prefixTransitionCheck 498=true := by decide +kernel
theorem prefix_transition_499 : prefixTransitionCheck 499=true := by decide +kernel
theorem prefix_transition_500 : prefixTransitionCheck 500=true := by decide +kernel
theorem prefix_transition_501 : prefixTransitionCheck 501=true := by decide +kernel
theorem prefix_transition_502 : prefixTransitionCheck 502=true := by decide +kernel
theorem prefix_transition_503 : prefixTransitionCheck 503=true := by decide +kernel
theorem prefix_transition_504 : prefixTransitionCheck 504=true := by decide +kernel
theorem prefix_transition_505 : prefixTransitionCheck 505=true := by decide +kernel
theorem prefix_transition_506 : prefixTransitionCheck 506=true := by decide +kernel
theorem prefix_transition_507 : prefixTransitionCheck 507=true := by decide +kernel
theorem prefix_transition_508 : prefixTransitionCheck 508=true := by decide +kernel
theorem prefix_transition_509 : prefixTransitionCheck 509=true := by decide +kernel
theorem prefix_transition_510 : prefixTransitionCheck 510=true := by decide +kernel
theorem prefix_transition_511 : prefixTransitionCheck 511=true := by decide +kernel

theorem prefix_transitions_31 (i : ℕ) (hi0 : 496 ≤ i) (hi1 : i < 512) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_496
  · exact prefix_transition_497
  · exact prefix_transition_498
  · exact prefix_transition_499
  · exact prefix_transition_500
  · exact prefix_transition_501
  · exact prefix_transition_502
  · exact prefix_transition_503
  · exact prefix_transition_504
  · exact prefix_transition_505
  · exact prefix_transition_506
  · exact prefix_transition_507
  · exact prefix_transition_508
  · exact prefix_transition_509
  · exact prefix_transition_510
  · exact prefix_transition_511

#print axioms prefix_transitions_31
end Erdos7No9Certificate
