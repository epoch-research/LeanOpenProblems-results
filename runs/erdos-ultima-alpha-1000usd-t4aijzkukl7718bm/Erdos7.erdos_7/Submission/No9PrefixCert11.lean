import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_176 : prefixTransitionCheck 176=true := by decide +kernel
theorem prefix_transition_177 : prefixTransitionCheck 177=true := by decide +kernel
theorem prefix_transition_178 : prefixTransitionCheck 178=true := by decide +kernel
theorem prefix_transition_179 : prefixTransitionCheck 179=true := by decide +kernel
theorem prefix_transition_180 : prefixTransitionCheck 180=true := by decide +kernel
theorem prefix_transition_181 : prefixTransitionCheck 181=true := by decide +kernel
theorem prefix_transition_182 : prefixTransitionCheck 182=true := by decide +kernel
theorem prefix_transition_183 : prefixTransitionCheck 183=true := by decide +kernel
theorem prefix_transition_184 : prefixTransitionCheck 184=true := by decide +kernel
theorem prefix_transition_185 : prefixTransitionCheck 185=true := by decide +kernel
theorem prefix_transition_186 : prefixTransitionCheck 186=true := by decide +kernel
theorem prefix_transition_187 : prefixTransitionCheck 187=true := by decide +kernel
theorem prefix_transition_188 : prefixTransitionCheck 188=true := by decide +kernel
theorem prefix_transition_189 : prefixTransitionCheck 189=true := by decide +kernel
theorem prefix_transition_190 : prefixTransitionCheck 190=true := by decide +kernel
theorem prefix_transition_191 : prefixTransitionCheck 191=true := by decide +kernel

theorem prefix_transitions_11 (i : ℕ) (hi0 : 176 ≤ i) (hi1 : i < 192) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_176
  · exact prefix_transition_177
  · exact prefix_transition_178
  · exact prefix_transition_179
  · exact prefix_transition_180
  · exact prefix_transition_181
  · exact prefix_transition_182
  · exact prefix_transition_183
  · exact prefix_transition_184
  · exact prefix_transition_185
  · exact prefix_transition_186
  · exact prefix_transition_187
  · exact prefix_transition_188
  · exact prefix_transition_189
  · exact prefix_transition_190
  · exact prefix_transition_191

#print axioms prefix_transitions_11
end Erdos7No9Certificate
