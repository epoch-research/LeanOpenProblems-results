import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_192 : prefixTransitionCheck 192=true := by decide +kernel
theorem prefix_transition_193 : prefixTransitionCheck 193=true := by decide +kernel
theorem prefix_transition_194 : prefixTransitionCheck 194=true := by decide +kernel
theorem prefix_transition_195 : prefixTransitionCheck 195=true := by decide +kernel
theorem prefix_transition_196 : prefixTransitionCheck 196=true := by decide +kernel
theorem prefix_transition_197 : prefixTransitionCheck 197=true := by decide +kernel
theorem prefix_transition_198 : prefixTransitionCheck 198=true := by decide +kernel
theorem prefix_transition_199 : prefixTransitionCheck 199=true := by decide +kernel
theorem prefix_transition_200 : prefixTransitionCheck 200=true := by decide +kernel
theorem prefix_transition_201 : prefixTransitionCheck 201=true := by decide +kernel
theorem prefix_transition_202 : prefixTransitionCheck 202=true := by decide +kernel
theorem prefix_transition_203 : prefixTransitionCheck 203=true := by decide +kernel
theorem prefix_transition_204 : prefixTransitionCheck 204=true := by decide +kernel
theorem prefix_transition_205 : prefixTransitionCheck 205=true := by decide +kernel
theorem prefix_transition_206 : prefixTransitionCheck 206=true := by decide +kernel
theorem prefix_transition_207 : prefixTransitionCheck 207=true := by decide +kernel

theorem prefix_transitions_12 (i : ℕ) (hi0 : 192 ≤ i) (hi1 : i < 208) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_192
  · exact prefix_transition_193
  · exact prefix_transition_194
  · exact prefix_transition_195
  · exact prefix_transition_196
  · exact prefix_transition_197
  · exact prefix_transition_198
  · exact prefix_transition_199
  · exact prefix_transition_200
  · exact prefix_transition_201
  · exact prefix_transition_202
  · exact prefix_transition_203
  · exact prefix_transition_204
  · exact prefix_transition_205
  · exact prefix_transition_206
  · exact prefix_transition_207

#print axioms prefix_transitions_12
end Erdos7No9Certificate
