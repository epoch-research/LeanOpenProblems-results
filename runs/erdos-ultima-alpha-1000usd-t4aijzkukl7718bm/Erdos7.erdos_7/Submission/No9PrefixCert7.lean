import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_112 : prefixTransitionCheck 112=true := by decide +kernel
theorem prefix_transition_113 : prefixTransitionCheck 113=true := by decide +kernel
theorem prefix_transition_114 : prefixTransitionCheck 114=true := by decide +kernel
theorem prefix_transition_115 : prefixTransitionCheck 115=true := by decide +kernel
theorem prefix_transition_116 : prefixTransitionCheck 116=true := by decide +kernel
theorem prefix_transition_117 : prefixTransitionCheck 117=true := by decide +kernel
theorem prefix_transition_118 : prefixTransitionCheck 118=true := by decide +kernel
theorem prefix_transition_119 : prefixTransitionCheck 119=true := by decide +kernel
theorem prefix_transition_120 : prefixTransitionCheck 120=true := by decide +kernel
theorem prefix_transition_121 : prefixTransitionCheck 121=true := by decide +kernel
theorem prefix_transition_122 : prefixTransitionCheck 122=true := by decide +kernel
theorem prefix_transition_123 : prefixTransitionCheck 123=true := by decide +kernel
theorem prefix_transition_124 : prefixTransitionCheck 124=true := by decide +kernel
theorem prefix_transition_125 : prefixTransitionCheck 125=true := by decide +kernel
theorem prefix_transition_126 : prefixTransitionCheck 126=true := by decide +kernel
theorem prefix_transition_127 : prefixTransitionCheck 127=true := by decide +kernel

theorem prefix_transitions_7 (i : ℕ) (hi0 : 112 ≤ i) (hi1 : i < 128) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_112
  · exact prefix_transition_113
  · exact prefix_transition_114
  · exact prefix_transition_115
  · exact prefix_transition_116
  · exact prefix_transition_117
  · exact prefix_transition_118
  · exact prefix_transition_119
  · exact prefix_transition_120
  · exact prefix_transition_121
  · exact prefix_transition_122
  · exact prefix_transition_123
  · exact prefix_transition_124
  · exact prefix_transition_125
  · exact prefix_transition_126
  · exact prefix_transition_127

#print axioms prefix_transitions_7
end Erdos7No9Certificate
