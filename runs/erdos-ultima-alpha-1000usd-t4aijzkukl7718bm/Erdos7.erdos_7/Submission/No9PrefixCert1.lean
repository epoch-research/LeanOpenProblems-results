import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_16 : prefixTransitionCheck 16=true := by decide +kernel
theorem prefix_transition_17 : prefixTransitionCheck 17=true := by decide +kernel
theorem prefix_transition_18 : prefixTransitionCheck 18=true := by decide +kernel
theorem prefix_transition_19 : prefixTransitionCheck 19=true := by decide +kernel
theorem prefix_transition_20 : prefixTransitionCheck 20=true := by decide +kernel
theorem prefix_transition_21 : prefixTransitionCheck 21=true := by decide +kernel
theorem prefix_transition_22 : prefixTransitionCheck 22=true := by decide +kernel
theorem prefix_transition_23 : prefixTransitionCheck 23=true := by decide +kernel
theorem prefix_transition_24 : prefixTransitionCheck 24=true := by decide +kernel
theorem prefix_transition_25 : prefixTransitionCheck 25=true := by decide +kernel
theorem prefix_transition_26 : prefixTransitionCheck 26=true := by decide +kernel
theorem prefix_transition_27 : prefixTransitionCheck 27=true := by decide +kernel
theorem prefix_transition_28 : prefixTransitionCheck 28=true := by decide +kernel
theorem prefix_transition_29 : prefixTransitionCheck 29=true := by decide +kernel
theorem prefix_transition_30 : prefixTransitionCheck 30=true := by decide +kernel
theorem prefix_transition_31 : prefixTransitionCheck 31=true := by decide +kernel

theorem prefix_transitions_1 (i : ℕ) (hi0 : 16 ≤ i) (hi1 : i < 32) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_16
  · exact prefix_transition_17
  · exact prefix_transition_18
  · exact prefix_transition_19
  · exact prefix_transition_20
  · exact prefix_transition_21
  · exact prefix_transition_22
  · exact prefix_transition_23
  · exact prefix_transition_24
  · exact prefix_transition_25
  · exact prefix_transition_26
  · exact prefix_transition_27
  · exact prefix_transition_28
  · exact prefix_transition_29
  · exact prefix_transition_30
  · exact prefix_transition_31

#print axioms prefix_transitions_1
end Erdos7No9Certificate
