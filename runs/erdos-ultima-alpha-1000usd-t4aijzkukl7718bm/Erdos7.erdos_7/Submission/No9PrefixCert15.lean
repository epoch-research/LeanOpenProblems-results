import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_240 : prefixTransitionCheck 240=true := by decide +kernel
theorem prefix_transition_241 : prefixTransitionCheck 241=true := by decide +kernel
theorem prefix_transition_242 : prefixTransitionCheck 242=true := by decide +kernel
theorem prefix_transition_243 : prefixTransitionCheck 243=true := by decide +kernel
theorem prefix_transition_244 : prefixTransitionCheck 244=true := by decide +kernel
theorem prefix_transition_245 : prefixTransitionCheck 245=true := by decide +kernel
theorem prefix_transition_246 : prefixTransitionCheck 246=true := by decide +kernel
theorem prefix_transition_247 : prefixTransitionCheck 247=true := by decide +kernel
theorem prefix_transition_248 : prefixTransitionCheck 248=true := by decide +kernel
theorem prefix_transition_249 : prefixTransitionCheck 249=true := by decide +kernel
theorem prefix_transition_250 : prefixTransitionCheck 250=true := by decide +kernel
theorem prefix_transition_251 : prefixTransitionCheck 251=true := by decide +kernel
theorem prefix_transition_252 : prefixTransitionCheck 252=true := by decide +kernel
theorem prefix_transition_253 : prefixTransitionCheck 253=true := by decide +kernel
theorem prefix_transition_254 : prefixTransitionCheck 254=true := by decide +kernel
theorem prefix_transition_255 : prefixTransitionCheck 255=true := by decide +kernel

theorem prefix_transitions_15 (i : ℕ) (hi0 : 240 ≤ i) (hi1 : i < 256) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_240
  · exact prefix_transition_241
  · exact prefix_transition_242
  · exact prefix_transition_243
  · exact prefix_transition_244
  · exact prefix_transition_245
  · exact prefix_transition_246
  · exact prefix_transition_247
  · exact prefix_transition_248
  · exact prefix_transition_249
  · exact prefix_transition_250
  · exact prefix_transition_251
  · exact prefix_transition_252
  · exact prefix_transition_253
  · exact prefix_transition_254
  · exact prefix_transition_255

#print axioms prefix_transitions_15
end Erdos7No9Certificate
