import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_256 : prefixTransitionCheck 256=true := by decide +kernel
theorem prefix_transition_257 : prefixTransitionCheck 257=true := by decide +kernel
theorem prefix_transition_258 : prefixTransitionCheck 258=true := by decide +kernel
theorem prefix_transition_259 : prefixTransitionCheck 259=true := by decide +kernel
theorem prefix_transition_260 : prefixTransitionCheck 260=true := by decide +kernel
theorem prefix_transition_261 : prefixTransitionCheck 261=true := by decide +kernel
theorem prefix_transition_262 : prefixTransitionCheck 262=true := by decide +kernel
theorem prefix_transition_263 : prefixTransitionCheck 263=true := by decide +kernel
theorem prefix_transition_264 : prefixTransitionCheck 264=true := by decide +kernel
theorem prefix_transition_265 : prefixTransitionCheck 265=true := by decide +kernel
theorem prefix_transition_266 : prefixTransitionCheck 266=true := by decide +kernel
theorem prefix_transition_267 : prefixTransitionCheck 267=true := by decide +kernel
theorem prefix_transition_268 : prefixTransitionCheck 268=true := by decide +kernel
theorem prefix_transition_269 : prefixTransitionCheck 269=true := by decide +kernel
theorem prefix_transition_270 : prefixTransitionCheck 270=true := by decide +kernel
theorem prefix_transition_271 : prefixTransitionCheck 271=true := by decide +kernel

theorem prefix_transitions_16 (i : ℕ) (hi0 : 256 ≤ i) (hi1 : i < 272) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_256
  · exact prefix_transition_257
  · exact prefix_transition_258
  · exact prefix_transition_259
  · exact prefix_transition_260
  · exact prefix_transition_261
  · exact prefix_transition_262
  · exact prefix_transition_263
  · exact prefix_transition_264
  · exact prefix_transition_265
  · exact prefix_transition_266
  · exact prefix_transition_267
  · exact prefix_transition_268
  · exact prefix_transition_269
  · exact prefix_transition_270
  · exact prefix_transition_271

#print axioms prefix_transitions_16
end Erdos7No9Certificate
