import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_0 : blockTransitionCheck 0=true := by decide +kernel
theorem block_transition_1 : blockTransitionCheck 1=true := by decide +kernel
theorem block_transition_2 : blockTransitionCheck 2=true := by decide +kernel
theorem block_transition_3 : blockTransitionCheck 3=true := by decide +kernel
theorem block_transition_4 : blockTransitionCheck 4=true := by decide +kernel
theorem block_transition_5 : blockTransitionCheck 5=true := by decide +kernel
theorem block_transition_6 : blockTransitionCheck 6=true := by decide +kernel
theorem block_transition_7 : blockTransitionCheck 7=true := by decide +kernel
theorem block_transition_8 : blockTransitionCheck 8=true := by decide +kernel
theorem block_transition_9 : blockTransitionCheck 9=true := by decide +kernel
theorem block_transition_10 : blockTransitionCheck 10=true := by decide +kernel
theorem block_transition_11 : blockTransitionCheck 11=true := by decide +kernel
theorem block_transition_12 : blockTransitionCheck 12=true := by decide +kernel
theorem block_transition_13 : blockTransitionCheck 13=true := by decide +kernel
theorem block_transition_14 : blockTransitionCheck 14=true := by decide +kernel
theorem block_transition_15 : blockTransitionCheck 15=true := by decide +kernel

theorem block_transitions_0 (i : ℕ) (hi0 : 0 ≤ i) (hi1 : i < 16) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_0
  · exact block_transition_1
  · exact block_transition_2
  · exact block_transition_3
  · exact block_transition_4
  · exact block_transition_5
  · exact block_transition_6
  · exact block_transition_7
  · exact block_transition_8
  · exact block_transition_9
  · exact block_transition_10
  · exact block_transition_11
  · exact block_transition_12
  · exact block_transition_13
  · exact block_transition_14
  · exact block_transition_15

#print axioms block_transitions_0
end Erdos7No9Certificate
