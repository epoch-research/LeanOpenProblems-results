import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_272 : prefixTransitionCheck 272=true := by decide +kernel
theorem prefix_transition_273 : prefixTransitionCheck 273=true := by decide +kernel
theorem prefix_transition_274 : prefixTransitionCheck 274=true := by decide +kernel
theorem prefix_transition_275 : prefixTransitionCheck 275=true := by decide +kernel
theorem prefix_transition_276 : prefixTransitionCheck 276=true := by decide +kernel
theorem prefix_transition_277 : prefixTransitionCheck 277=true := by decide +kernel
theorem prefix_transition_278 : prefixTransitionCheck 278=true := by decide +kernel
theorem prefix_transition_279 : prefixTransitionCheck 279=true := by decide +kernel
theorem prefix_transition_280 : prefixTransitionCheck 280=true := by decide +kernel
theorem prefix_transition_281 : prefixTransitionCheck 281=true := by decide +kernel
theorem prefix_transition_282 : prefixTransitionCheck 282=true := by decide +kernel
theorem prefix_transition_283 : prefixTransitionCheck 283=true := by decide +kernel
theorem prefix_transition_284 : prefixTransitionCheck 284=true := by decide +kernel
theorem prefix_transition_285 : prefixTransitionCheck 285=true := by decide +kernel
theorem prefix_transition_286 : prefixTransitionCheck 286=true := by decide +kernel
theorem prefix_transition_287 : prefixTransitionCheck 287=true := by decide +kernel

theorem prefix_transitions_17 (i : ℕ) (hi0 : 272 ≤ i) (hi1 : i < 288) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_272
  · exact prefix_transition_273
  · exact prefix_transition_274
  · exact prefix_transition_275
  · exact prefix_transition_276
  · exact prefix_transition_277
  · exact prefix_transition_278
  · exact prefix_transition_279
  · exact prefix_transition_280
  · exact prefix_transition_281
  · exact prefix_transition_282
  · exact prefix_transition_283
  · exact prefix_transition_284
  · exact prefix_transition_285
  · exact prefix_transition_286
  · exact prefix_transition_287

#print axioms prefix_transitions_17
end Erdos7No9Certificate
