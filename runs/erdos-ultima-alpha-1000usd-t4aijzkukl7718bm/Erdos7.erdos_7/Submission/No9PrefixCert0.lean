import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_0 : prefixTransitionCheck 0=true := by decide +kernel
theorem prefix_transition_1 : prefixTransitionCheck 1=true := by decide +kernel
theorem prefix_transition_2 : prefixTransitionCheck 2=true := by decide +kernel
theorem prefix_transition_3 : prefixTransitionCheck 3=true := by decide +kernel
theorem prefix_transition_4 : prefixTransitionCheck 4=true := by decide +kernel
theorem prefix_transition_5 : prefixTransitionCheck 5=true := by decide +kernel
theorem prefix_transition_6 : prefixTransitionCheck 6=true := by decide +kernel
theorem prefix_transition_7 : prefixTransitionCheck 7=true := by decide +kernel
theorem prefix_transition_8 : prefixTransitionCheck 8=true := by decide +kernel
theorem prefix_transition_9 : prefixTransitionCheck 9=true := by decide +kernel
theorem prefix_transition_10 : prefixTransitionCheck 10=true := by decide +kernel
theorem prefix_transition_11 : prefixTransitionCheck 11=true := by decide +kernel
theorem prefix_transition_12 : prefixTransitionCheck 12=true := by decide +kernel
theorem prefix_transition_13 : prefixTransitionCheck 13=true := by decide +kernel
theorem prefix_transition_14 : prefixTransitionCheck 14=true := by decide +kernel
theorem prefix_transition_15 : prefixTransitionCheck 15=true := by decide +kernel

theorem prefix_transitions_0 (i : ℕ) (hi0 : 0 ≤ i) (hi1 : i < 16) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_0
  · exact prefix_transition_1
  · exact prefix_transition_2
  · exact prefix_transition_3
  · exact prefix_transition_4
  · exact prefix_transition_5
  · exact prefix_transition_6
  · exact prefix_transition_7
  · exact prefix_transition_8
  · exact prefix_transition_9
  · exact prefix_transition_10
  · exact prefix_transition_11
  · exact prefix_transition_12
  · exact prefix_transition_13
  · exact prefix_transition_14
  · exact prefix_transition_15

#print axioms prefix_transitions_0
end Erdos7No9Certificate
