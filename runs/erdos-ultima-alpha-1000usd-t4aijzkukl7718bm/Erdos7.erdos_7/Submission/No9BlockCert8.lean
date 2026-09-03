import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_128 : blockTransitionCheck 128=true := by decide +kernel
theorem block_transition_129 : blockTransitionCheck 129=true := by decide +kernel
theorem block_transition_130 : blockTransitionCheck 130=true := by decide +kernel
theorem block_transition_131 : blockTransitionCheck 131=true := by decide +kernel
theorem block_transition_132 : blockTransitionCheck 132=true := by decide +kernel
theorem block_transition_133 : blockTransitionCheck 133=true := by decide +kernel
theorem block_transition_134 : blockTransitionCheck 134=true := by decide +kernel
theorem block_transition_135 : blockTransitionCheck 135=true := by decide +kernel
theorem block_transition_136 : blockTransitionCheck 136=true := by decide +kernel
theorem block_transition_137 : blockTransitionCheck 137=true := by decide +kernel
theorem block_transition_138 : blockTransitionCheck 138=true := by decide +kernel
theorem block_transition_139 : blockTransitionCheck 139=true := by decide +kernel
theorem block_transition_140 : blockTransitionCheck 140=true := by decide +kernel
theorem block_transition_141 : blockTransitionCheck 141=true := by decide +kernel
theorem block_transition_142 : blockTransitionCheck 142=true := by decide +kernel
theorem block_transition_143 : blockTransitionCheck 143=true := by decide +kernel

theorem block_transitions_8 (i : ℕ) (hi0 : 128 ≤ i) (hi1 : i < 144) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_128
  · exact block_transition_129
  · exact block_transition_130
  · exact block_transition_131
  · exact block_transition_132
  · exact block_transition_133
  · exact block_transition_134
  · exact block_transition_135
  · exact block_transition_136
  · exact block_transition_137
  · exact block_transition_138
  · exact block_transition_139
  · exact block_transition_140
  · exact block_transition_141
  · exact block_transition_142
  · exact block_transition_143

#print axioms block_transitions_8
end Erdos7No9Certificate
