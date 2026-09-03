import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_608 : prefixTransitionCheck 608=true := by decide +kernel
theorem prefix_transition_609 : prefixTransitionCheck 609=true := by decide +kernel
theorem prefix_transition_610 : prefixTransitionCheck 610=true := by decide +kernel
theorem prefix_transition_611 : prefixTransitionCheck 611=true := by decide +kernel
theorem prefix_transition_612 : prefixTransitionCheck 612=true := by decide +kernel
theorem prefix_transition_613 : prefixTransitionCheck 613=true := by decide +kernel
theorem prefix_transition_614 : prefixTransitionCheck 614=true := by decide +kernel
theorem prefix_transition_615 : prefixTransitionCheck 615=true := by decide +kernel
theorem prefix_transition_616 : prefixTransitionCheck 616=true := by decide +kernel
theorem prefix_transition_617 : prefixTransitionCheck 617=true := by decide +kernel
theorem prefix_transition_618 : prefixTransitionCheck 618=true := by decide +kernel
theorem prefix_transition_619 : prefixTransitionCheck 619=true := by decide +kernel
theorem prefix_transition_620 : prefixTransitionCheck 620=true := by decide +kernel
theorem prefix_transition_621 : prefixTransitionCheck 621=true := by decide +kernel
theorem prefix_transition_622 : prefixTransitionCheck 622=true := by decide +kernel
theorem prefix_transition_623 : prefixTransitionCheck 623=true := by decide +kernel

theorem prefix_transitions_38 (i : ℕ) (hi0 : 608 ≤ i) (hi1 : i < 624) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_608
  · exact prefix_transition_609
  · exact prefix_transition_610
  · exact prefix_transition_611
  · exact prefix_transition_612
  · exact prefix_transition_613
  · exact prefix_transition_614
  · exact prefix_transition_615
  · exact prefix_transition_616
  · exact prefix_transition_617
  · exact prefix_transition_618
  · exact prefix_transition_619
  · exact prefix_transition_620
  · exact prefix_transition_621
  · exact prefix_transition_622
  · exact prefix_transition_623

#print axioms prefix_transitions_38
end Erdos7No9Certificate
