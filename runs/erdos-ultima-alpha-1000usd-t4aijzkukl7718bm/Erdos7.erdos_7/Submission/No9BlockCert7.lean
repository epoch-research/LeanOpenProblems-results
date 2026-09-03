import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_112 : blockTransitionCheck 112=true := by decide +kernel
theorem block_transition_113 : blockTransitionCheck 113=true := by decide +kernel
theorem block_transition_114 : blockTransitionCheck 114=true := by decide +kernel
theorem block_transition_115 : blockTransitionCheck 115=true := by decide +kernel
theorem block_transition_116 : blockTransitionCheck 116=true := by decide +kernel
theorem block_transition_117 : blockTransitionCheck 117=true := by decide +kernel
theorem block_transition_118 : blockTransitionCheck 118=true := by decide +kernel
theorem block_transition_119 : blockTransitionCheck 119=true := by decide +kernel
theorem block_transition_120 : blockTransitionCheck 120=true := by decide +kernel
theorem block_transition_121 : blockTransitionCheck 121=true := by decide +kernel
theorem block_transition_122 : blockTransitionCheck 122=true := by decide +kernel
theorem block_transition_123 : blockTransitionCheck 123=true := by decide +kernel
theorem block_transition_124 : blockTransitionCheck 124=true := by decide +kernel
theorem block_transition_125 : blockTransitionCheck 125=true := by decide +kernel
theorem block_transition_126 : blockTransitionCheck 126=true := by decide +kernel
theorem block_transition_127 : blockTransitionCheck 127=true := by decide +kernel

theorem block_transitions_7 (i : ℕ) (hi0 : 112 ≤ i) (hi1 : i < 128) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_112
  · exact block_transition_113
  · exact block_transition_114
  · exact block_transition_115
  · exact block_transition_116
  · exact block_transition_117
  · exact block_transition_118
  · exact block_transition_119
  · exact block_transition_120
  · exact block_transition_121
  · exact block_transition_122
  · exact block_transition_123
  · exact block_transition_124
  · exact block_transition_125
  · exact block_transition_126
  · exact block_transition_127

#print axioms block_transitions_7
end Erdos7No9Certificate
