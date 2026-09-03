import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_272 : blockTransitionCheck 272=true := by decide +kernel
theorem block_transition_273 : blockTransitionCheck 273=true := by decide +kernel
theorem block_transition_274 : blockTransitionCheck 274=true := by decide +kernel
theorem block_transition_275 : blockTransitionCheck 275=true := by decide +kernel
theorem block_transition_276 : blockTransitionCheck 276=true := by decide +kernel
theorem block_transition_277 : blockTransitionCheck 277=true := by decide +kernel
theorem block_transition_278 : blockTransitionCheck 278=true := by decide +kernel
theorem block_transition_279 : blockTransitionCheck 279=true := by decide +kernel
theorem block_transition_280 : blockTransitionCheck 280=true := by decide +kernel
theorem block_transition_281 : blockTransitionCheck 281=true := by decide +kernel
theorem block_transition_282 : blockTransitionCheck 282=true := by decide +kernel
theorem block_transition_283 : blockTransitionCheck 283=true := by decide +kernel
theorem block_transition_284 : blockTransitionCheck 284=true := by decide +kernel
theorem block_transition_285 : blockTransitionCheck 285=true := by decide +kernel
theorem block_transition_286 : blockTransitionCheck 286=true := by decide +kernel
theorem block_transition_287 : blockTransitionCheck 287=true := by decide +kernel

theorem block_transitions_17 (i : ℕ) (hi0 : 272 ≤ i) (hi1 : i < 288) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_272
  · exact block_transition_273
  · exact block_transition_274
  · exact block_transition_275
  · exact block_transition_276
  · exact block_transition_277
  · exact block_transition_278
  · exact block_transition_279
  · exact block_transition_280
  · exact block_transition_281
  · exact block_transition_282
  · exact block_transition_283
  · exact block_transition_284
  · exact block_transition_285
  · exact block_transition_286
  · exact block_transition_287

#print axioms block_transitions_17
end Erdos7No9Certificate
