import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_592 : prefixTransitionCheck 592=true := by decide +kernel
theorem prefix_transition_593 : prefixTransitionCheck 593=true := by decide +kernel
theorem prefix_transition_594 : prefixTransitionCheck 594=true := by decide +kernel
theorem prefix_transition_595 : prefixTransitionCheck 595=true := by decide +kernel
theorem prefix_transition_596 : prefixTransitionCheck 596=true := by decide +kernel
theorem prefix_transition_597 : prefixTransitionCheck 597=true := by decide +kernel
theorem prefix_transition_598 : prefixTransitionCheck 598=true := by decide +kernel
theorem prefix_transition_599 : prefixTransitionCheck 599=true := by decide +kernel
theorem prefix_transition_600 : prefixTransitionCheck 600=true := by decide +kernel
theorem prefix_transition_601 : prefixTransitionCheck 601=true := by decide +kernel
theorem prefix_transition_602 : prefixTransitionCheck 602=true := by decide +kernel
theorem prefix_transition_603 : prefixTransitionCheck 603=true := by decide +kernel
theorem prefix_transition_604 : prefixTransitionCheck 604=true := by decide +kernel
theorem prefix_transition_605 : prefixTransitionCheck 605=true := by decide +kernel
theorem prefix_transition_606 : prefixTransitionCheck 606=true := by decide +kernel
theorem prefix_transition_607 : prefixTransitionCheck 607=true := by decide +kernel

theorem prefix_transitions_37 (i : ℕ) (hi0 : 592 ≤ i) (hi1 : i < 608) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_592
  · exact prefix_transition_593
  · exact prefix_transition_594
  · exact prefix_transition_595
  · exact prefix_transition_596
  · exact prefix_transition_597
  · exact prefix_transition_598
  · exact prefix_transition_599
  · exact prefix_transition_600
  · exact prefix_transition_601
  · exact prefix_transition_602
  · exact prefix_transition_603
  · exact prefix_transition_604
  · exact prefix_transition_605
  · exact prefix_transition_606
  · exact prefix_transition_607

#print axioms prefix_transitions_37
end Erdos7No9Certificate
