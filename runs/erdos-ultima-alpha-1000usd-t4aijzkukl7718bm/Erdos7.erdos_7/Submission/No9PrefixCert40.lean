import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_640 : prefixTransitionCheck 640=true := by decide +kernel
theorem prefix_transition_641 : prefixTransitionCheck 641=true := by decide +kernel
theorem prefix_transition_642 : prefixTransitionCheck 642=true := by decide +kernel
theorem prefix_transition_643 : prefixTransitionCheck 643=true := by decide +kernel
theorem prefix_transition_644 : prefixTransitionCheck 644=true := by decide +kernel
theorem prefix_transition_645 : prefixTransitionCheck 645=true := by decide +kernel
theorem prefix_transition_646 : prefixTransitionCheck 646=true := by decide +kernel
theorem prefix_transition_647 : prefixTransitionCheck 647=true := by decide +kernel
theorem prefix_transition_648 : prefixTransitionCheck 648=true := by decide +kernel
theorem prefix_transition_649 : prefixTransitionCheck 649=true := by decide +kernel
theorem prefix_transition_650 : prefixTransitionCheck 650=true := by decide +kernel
theorem prefix_transition_651 : prefixTransitionCheck 651=true := by decide +kernel
theorem prefix_transition_652 : prefixTransitionCheck 652=true := by decide +kernel
theorem prefix_transition_653 : prefixTransitionCheck 653=true := by decide +kernel
theorem prefix_transition_654 : prefixTransitionCheck 654=true := by decide +kernel
theorem prefix_transition_655 : prefixTransitionCheck 655=true := by decide +kernel

theorem prefix_transitions_40 (i : ℕ) (hi0 : 640 ≤ i) (hi1 : i < 656) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_640
  · exact prefix_transition_641
  · exact prefix_transition_642
  · exact prefix_transition_643
  · exact prefix_transition_644
  · exact prefix_transition_645
  · exact prefix_transition_646
  · exact prefix_transition_647
  · exact prefix_transition_648
  · exact prefix_transition_649
  · exact prefix_transition_650
  · exact prefix_transition_651
  · exact prefix_transition_652
  · exact prefix_transition_653
  · exact prefix_transition_654
  · exact prefix_transition_655

#print axioms prefix_transitions_40
end Erdos7No9Certificate
