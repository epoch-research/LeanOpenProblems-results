import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_128 : prefixTransitionCheck 128=true := by decide +kernel
theorem prefix_transition_129 : prefixTransitionCheck 129=true := by decide +kernel
theorem prefix_transition_130 : prefixTransitionCheck 130=true := by decide +kernel
theorem prefix_transition_131 : prefixTransitionCheck 131=true := by decide +kernel
theorem prefix_transition_132 : prefixTransitionCheck 132=true := by decide +kernel
theorem prefix_transition_133 : prefixTransitionCheck 133=true := by decide +kernel
theorem prefix_transition_134 : prefixTransitionCheck 134=true := by decide +kernel
theorem prefix_transition_135 : prefixTransitionCheck 135=true := by decide +kernel
theorem prefix_transition_136 : prefixTransitionCheck 136=true := by decide +kernel
theorem prefix_transition_137 : prefixTransitionCheck 137=true := by decide +kernel
theorem prefix_transition_138 : prefixTransitionCheck 138=true := by decide +kernel
theorem prefix_transition_139 : prefixTransitionCheck 139=true := by decide +kernel
theorem prefix_transition_140 : prefixTransitionCheck 140=true := by decide +kernel
theorem prefix_transition_141 : prefixTransitionCheck 141=true := by decide +kernel
theorem prefix_transition_142 : prefixTransitionCheck 142=true := by decide +kernel
theorem prefix_transition_143 : prefixTransitionCheck 143=true := by decide +kernel

theorem prefix_transitions_8 (i : ℕ) (hi0 : 128 ≤ i) (hi1 : i < 144) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_128
  · exact prefix_transition_129
  · exact prefix_transition_130
  · exact prefix_transition_131
  · exact prefix_transition_132
  · exact prefix_transition_133
  · exact prefix_transition_134
  · exact prefix_transition_135
  · exact prefix_transition_136
  · exact prefix_transition_137
  · exact prefix_transition_138
  · exact prefix_transition_139
  · exact prefix_transition_140
  · exact prefix_transition_141
  · exact prefix_transition_142
  · exact prefix_transition_143

#print axioms prefix_transitions_8
end Erdos7No9Certificate
