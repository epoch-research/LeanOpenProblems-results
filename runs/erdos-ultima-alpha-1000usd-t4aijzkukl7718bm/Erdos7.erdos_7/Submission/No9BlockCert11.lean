import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_176 : blockTransitionCheck 176=true := by decide +kernel
theorem block_transition_177 : blockTransitionCheck 177=true := by decide +kernel
theorem block_transition_178 : blockTransitionCheck 178=true := by decide +kernel
theorem block_transition_179 : blockTransitionCheck 179=true := by decide +kernel
theorem block_transition_180 : blockTransitionCheck 180=true := by decide +kernel
theorem block_transition_181 : blockTransitionCheck 181=true := by decide +kernel
theorem block_transition_182 : blockTransitionCheck 182=true := by decide +kernel
theorem block_transition_183 : blockTransitionCheck 183=true := by decide +kernel
theorem block_transition_184 : blockTransitionCheck 184=true := by decide +kernel
theorem block_transition_185 : blockTransitionCheck 185=true := by decide +kernel
theorem block_transition_186 : blockTransitionCheck 186=true := by decide +kernel
theorem block_transition_187 : blockTransitionCheck 187=true := by decide +kernel
theorem block_transition_188 : blockTransitionCheck 188=true := by decide +kernel
theorem block_transition_189 : blockTransitionCheck 189=true := by decide +kernel
theorem block_transition_190 : blockTransitionCheck 190=true := by decide +kernel
theorem block_transition_191 : blockTransitionCheck 191=true := by decide +kernel

theorem block_transitions_11 (i : ℕ) (hi0 : 176 ≤ i) (hi1 : i < 192) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_176
  · exact block_transition_177
  · exact block_transition_178
  · exact block_transition_179
  · exact block_transition_180
  · exact block_transition_181
  · exact block_transition_182
  · exact block_transition_183
  · exact block_transition_184
  · exact block_transition_185
  · exact block_transition_186
  · exact block_transition_187
  · exact block_transition_188
  · exact block_transition_189
  · exact block_transition_190
  · exact block_transition_191

#print axioms block_transitions_11
end Erdos7No9Certificate
