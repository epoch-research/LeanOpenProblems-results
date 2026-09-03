import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_224 : blockTransitionCheck 224=true := by decide +kernel
theorem block_transition_225 : blockTransitionCheck 225=true := by decide +kernel
theorem block_transition_226 : blockTransitionCheck 226=true := by decide +kernel
theorem block_transition_227 : blockTransitionCheck 227=true := by decide +kernel
theorem block_transition_228 : blockTransitionCheck 228=true := by decide +kernel
theorem block_transition_229 : blockTransitionCheck 229=true := by decide +kernel
theorem block_transition_230 : blockTransitionCheck 230=true := by decide +kernel
theorem block_transition_231 : blockTransitionCheck 231=true := by decide +kernel
theorem block_transition_232 : blockTransitionCheck 232=true := by decide +kernel
theorem block_transition_233 : blockTransitionCheck 233=true := by decide +kernel
theorem block_transition_234 : blockTransitionCheck 234=true := by decide +kernel
theorem block_transition_235 : blockTransitionCheck 235=true := by decide +kernel
theorem block_transition_236 : blockTransitionCheck 236=true := by decide +kernel
theorem block_transition_237 : blockTransitionCheck 237=true := by decide +kernel
theorem block_transition_238 : blockTransitionCheck 238=true := by decide +kernel
theorem block_transition_239 : blockTransitionCheck 239=true := by decide +kernel

theorem block_transitions_14 (i : ℕ) (hi0 : 224 ≤ i) (hi1 : i < 240) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_224
  · exact block_transition_225
  · exact block_transition_226
  · exact block_transition_227
  · exact block_transition_228
  · exact block_transition_229
  · exact block_transition_230
  · exact block_transition_231
  · exact block_transition_232
  · exact block_transition_233
  · exact block_transition_234
  · exact block_transition_235
  · exact block_transition_236
  · exact block_transition_237
  · exact block_transition_238
  · exact block_transition_239

#print axioms block_transitions_14
end Erdos7No9Certificate
