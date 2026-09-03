import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_224 : prefixTransitionCheck 224=true := by decide +kernel
theorem prefix_transition_225 : prefixTransitionCheck 225=true := by decide +kernel
theorem prefix_transition_226 : prefixTransitionCheck 226=true := by decide +kernel
theorem prefix_transition_227 : prefixTransitionCheck 227=true := by decide +kernel
theorem prefix_transition_228 : prefixTransitionCheck 228=true := by decide +kernel
theorem prefix_transition_229 : prefixTransitionCheck 229=true := by decide +kernel
theorem prefix_transition_230 : prefixTransitionCheck 230=true := by decide +kernel
theorem prefix_transition_231 : prefixTransitionCheck 231=true := by decide +kernel
theorem prefix_transition_232 : prefixTransitionCheck 232=true := by decide +kernel
theorem prefix_transition_233 : prefixTransitionCheck 233=true := by decide +kernel
theorem prefix_transition_234 : prefixTransitionCheck 234=true := by decide +kernel
theorem prefix_transition_235 : prefixTransitionCheck 235=true := by decide +kernel
theorem prefix_transition_236 : prefixTransitionCheck 236=true := by decide +kernel
theorem prefix_transition_237 : prefixTransitionCheck 237=true := by decide +kernel
theorem prefix_transition_238 : prefixTransitionCheck 238=true := by decide +kernel
theorem prefix_transition_239 : prefixTransitionCheck 239=true := by decide +kernel

theorem prefix_transitions_14 (i : ℕ) (hi0 : 224 ≤ i) (hi1 : i < 240) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_224
  · exact prefix_transition_225
  · exact prefix_transition_226
  · exact prefix_transition_227
  · exact prefix_transition_228
  · exact prefix_transition_229
  · exact prefix_transition_230
  · exact prefix_transition_231
  · exact prefix_transition_232
  · exact prefix_transition_233
  · exact prefix_transition_234
  · exact prefix_transition_235
  · exact prefix_transition_236
  · exact prefix_transition_237
  · exact prefix_transition_238
  · exact prefix_transition_239

#print axioms prefix_transitions_14
end Erdos7No9Certificate
