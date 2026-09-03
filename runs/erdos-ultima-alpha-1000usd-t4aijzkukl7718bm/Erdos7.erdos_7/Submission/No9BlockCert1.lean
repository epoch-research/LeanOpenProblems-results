import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_16 : blockTransitionCheck 16=true := by decide +kernel
theorem block_transition_17 : blockTransitionCheck 17=true := by decide +kernel
theorem block_transition_18 : blockTransitionCheck 18=true := by decide +kernel
theorem block_transition_19 : blockTransitionCheck 19=true := by decide +kernel
theorem block_transition_20 : blockTransitionCheck 20=true := by decide +kernel
theorem block_transition_21 : blockTransitionCheck 21=true := by decide +kernel
theorem block_transition_22 : blockTransitionCheck 22=true := by decide +kernel
theorem block_transition_23 : blockTransitionCheck 23=true := by decide +kernel
theorem block_transition_24 : blockTransitionCheck 24=true := by decide +kernel
theorem block_transition_25 : blockTransitionCheck 25=true := by decide +kernel
theorem block_transition_26 : blockTransitionCheck 26=true := by decide +kernel
theorem block_transition_27 : blockTransitionCheck 27=true := by decide +kernel
theorem block_transition_28 : blockTransitionCheck 28=true := by decide +kernel
theorem block_transition_29 : blockTransitionCheck 29=true := by decide +kernel
theorem block_transition_30 : blockTransitionCheck 30=true := by decide +kernel
theorem block_transition_31 : blockTransitionCheck 31=true := by decide +kernel

theorem block_transitions_1 (i : ℕ) (hi0 : 16 ≤ i) (hi1 : i < 32) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_16
  · exact block_transition_17
  · exact block_transition_18
  · exact block_transition_19
  · exact block_transition_20
  · exact block_transition_21
  · exact block_transition_22
  · exact block_transition_23
  · exact block_transition_24
  · exact block_transition_25
  · exact block_transition_26
  · exact block_transition_27
  · exact block_transition_28
  · exact block_transition_29
  · exact block_transition_30
  · exact block_transition_31

#print axioms block_transitions_1
end Erdos7No9Certificate
