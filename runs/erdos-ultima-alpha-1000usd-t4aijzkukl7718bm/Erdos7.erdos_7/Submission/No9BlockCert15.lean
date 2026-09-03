import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_240 : blockTransitionCheck 240=true := by decide +kernel
theorem block_transition_241 : blockTransitionCheck 241=true := by decide +kernel
theorem block_transition_242 : blockTransitionCheck 242=true := by decide +kernel
theorem block_transition_243 : blockTransitionCheck 243=true := by decide +kernel
theorem block_transition_244 : blockTransitionCheck 244=true := by decide +kernel
theorem block_transition_245 : blockTransitionCheck 245=true := by decide +kernel
theorem block_transition_246 : blockTransitionCheck 246=true := by decide +kernel
theorem block_transition_247 : blockTransitionCheck 247=true := by decide +kernel
theorem block_transition_248 : blockTransitionCheck 248=true := by decide +kernel
theorem block_transition_249 : blockTransitionCheck 249=true := by decide +kernel
theorem block_transition_250 : blockTransitionCheck 250=true := by decide +kernel
theorem block_transition_251 : blockTransitionCheck 251=true := by decide +kernel
theorem block_transition_252 : blockTransitionCheck 252=true := by decide +kernel
theorem block_transition_253 : blockTransitionCheck 253=true := by decide +kernel
theorem block_transition_254 : blockTransitionCheck 254=true := by decide +kernel
theorem block_transition_255 : blockTransitionCheck 255=true := by decide +kernel

theorem block_transitions_15 (i : ℕ) (hi0 : 240 ≤ i) (hi1 : i < 256) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_240
  · exact block_transition_241
  · exact block_transition_242
  · exact block_transition_243
  · exact block_transition_244
  · exact block_transition_245
  · exact block_transition_246
  · exact block_transition_247
  · exact block_transition_248
  · exact block_transition_249
  · exact block_transition_250
  · exact block_transition_251
  · exact block_transition_252
  · exact block_transition_253
  · exact block_transition_254
  · exact block_transition_255

#print axioms block_transitions_15
end Erdos7No9Certificate
