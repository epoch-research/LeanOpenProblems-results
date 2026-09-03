import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_656 : prefixTransitionCheck 656=true := by decide +kernel
theorem prefix_transition_657 : prefixTransitionCheck 657=true := by decide +kernel
theorem prefix_transition_658 : prefixTransitionCheck 658=true := by decide +kernel
theorem prefix_transition_659 : prefixTransitionCheck 659=true := by decide +kernel
theorem prefix_transition_660 : prefixTransitionCheck 660=true := by decide +kernel
theorem prefix_transition_661 : prefixTransitionCheck 661=true := by decide +kernel
theorem prefix_transition_662 : prefixTransitionCheck 662=true := by decide +kernel
theorem prefix_transition_663 : prefixTransitionCheck 663=true := by decide +kernel
theorem prefix_transition_664 : prefixTransitionCheck 664=true := by decide +kernel
theorem prefix_transition_665 : prefixTransitionCheck 665=true := by decide +kernel
theorem prefix_transition_666 : prefixTransitionCheck 666=true := by decide +kernel
theorem prefix_transition_667 : prefixTransitionCheck 667=true := by decide +kernel

theorem prefix_transitions_41 (i : ℕ) (hi0 : 656 ≤ i) (hi1 : i < 668) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_656
  · exact prefix_transition_657
  · exact prefix_transition_658
  · exact prefix_transition_659
  · exact prefix_transition_660
  · exact prefix_transition_661
  · exact prefix_transition_662
  · exact prefix_transition_663
  · exact prefix_transition_664
  · exact prefix_transition_665
  · exact prefix_transition_666
  · exact prefix_transition_667

#print axioms prefix_transitions_41
end Erdos7No9Certificate
