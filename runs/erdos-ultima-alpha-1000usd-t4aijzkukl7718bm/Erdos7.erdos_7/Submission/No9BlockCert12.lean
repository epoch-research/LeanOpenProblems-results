import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_192 : blockTransitionCheck 192=true := by decide +kernel
theorem block_transition_193 : blockTransitionCheck 193=true := by decide +kernel
theorem block_transition_194 : blockTransitionCheck 194=true := by decide +kernel
theorem block_transition_195 : blockTransitionCheck 195=true := by decide +kernel
theorem block_transition_196 : blockTransitionCheck 196=true := by decide +kernel
theorem block_transition_197 : blockTransitionCheck 197=true := by decide +kernel
theorem block_transition_198 : blockTransitionCheck 198=true := by decide +kernel
theorem block_transition_199 : blockTransitionCheck 199=true := by decide +kernel
theorem block_transition_200 : blockTransitionCheck 200=true := by decide +kernel
theorem block_transition_201 : blockTransitionCheck 201=true := by decide +kernel
theorem block_transition_202 : blockTransitionCheck 202=true := by decide +kernel
theorem block_transition_203 : blockTransitionCheck 203=true := by decide +kernel
theorem block_transition_204 : blockTransitionCheck 204=true := by decide +kernel
theorem block_transition_205 : blockTransitionCheck 205=true := by decide +kernel
theorem block_transition_206 : blockTransitionCheck 206=true := by decide +kernel
theorem block_transition_207 : blockTransitionCheck 207=true := by decide +kernel

theorem block_transitions_12 (i : ℕ) (hi0 : 192 ≤ i) (hi1 : i < 208) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_192
  · exact block_transition_193
  · exact block_transition_194
  · exact block_transition_195
  · exact block_transition_196
  · exact block_transition_197
  · exact block_transition_198
  · exact block_transition_199
  · exact block_transition_200
  · exact block_transition_201
  · exact block_transition_202
  · exact block_transition_203
  · exact block_transition_204
  · exact block_transition_205
  · exact block_transition_206
  · exact block_transition_207

#print axioms block_transitions_12
end Erdos7No9Certificate
