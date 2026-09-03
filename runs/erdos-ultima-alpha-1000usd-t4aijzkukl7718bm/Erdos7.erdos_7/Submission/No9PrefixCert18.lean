import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_288 : prefixTransitionCheck 288=true := by decide +kernel
theorem prefix_transition_289 : prefixTransitionCheck 289=true := by decide +kernel
theorem prefix_transition_290 : prefixTransitionCheck 290=true := by decide +kernel
theorem prefix_transition_291 : prefixTransitionCheck 291=true := by decide +kernel
theorem prefix_transition_292 : prefixTransitionCheck 292=true := by decide +kernel
theorem prefix_transition_293 : prefixTransitionCheck 293=true := by decide +kernel
theorem prefix_transition_294 : prefixTransitionCheck 294=true := by decide +kernel
theorem prefix_transition_295 : prefixTransitionCheck 295=true := by decide +kernel
theorem prefix_transition_296 : prefixTransitionCheck 296=true := by decide +kernel
theorem prefix_transition_297 : prefixTransitionCheck 297=true := by decide +kernel
theorem prefix_transition_298 : prefixTransitionCheck 298=true := by decide +kernel
theorem prefix_transition_299 : prefixTransitionCheck 299=true := by decide +kernel
theorem prefix_transition_300 : prefixTransitionCheck 300=true := by decide +kernel
theorem prefix_transition_301 : prefixTransitionCheck 301=true := by decide +kernel
theorem prefix_transition_302 : prefixTransitionCheck 302=true := by decide +kernel
theorem prefix_transition_303 : prefixTransitionCheck 303=true := by decide +kernel

theorem prefix_transitions_18 (i : ℕ) (hi0 : 288 ≤ i) (hi1 : i < 304) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_288
  · exact prefix_transition_289
  · exact prefix_transition_290
  · exact prefix_transition_291
  · exact prefix_transition_292
  · exact prefix_transition_293
  · exact prefix_transition_294
  · exact prefix_transition_295
  · exact prefix_transition_296
  · exact prefix_transition_297
  · exact prefix_transition_298
  · exact prefix_transition_299
  · exact prefix_transition_300
  · exact prefix_transition_301
  · exact prefix_transition_302
  · exact prefix_transition_303

#print axioms prefix_transitions_18
end Erdos7No9Certificate
