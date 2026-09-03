import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_320 : prefixTransitionCheck 320=true := by decide +kernel
theorem prefix_transition_321 : prefixTransitionCheck 321=true := by decide +kernel
theorem prefix_transition_322 : prefixTransitionCheck 322=true := by decide +kernel
theorem prefix_transition_323 : prefixTransitionCheck 323=true := by decide +kernel
theorem prefix_transition_324 : prefixTransitionCheck 324=true := by decide +kernel
theorem prefix_transition_325 : prefixTransitionCheck 325=true := by decide +kernel
theorem prefix_transition_326 : prefixTransitionCheck 326=true := by decide +kernel
theorem prefix_transition_327 : prefixTransitionCheck 327=true := by decide +kernel
theorem prefix_transition_328 : prefixTransitionCheck 328=true := by decide +kernel
theorem prefix_transition_329 : prefixTransitionCheck 329=true := by decide +kernel
theorem prefix_transition_330 : prefixTransitionCheck 330=true := by decide +kernel
theorem prefix_transition_331 : prefixTransitionCheck 331=true := by decide +kernel
theorem prefix_transition_332 : prefixTransitionCheck 332=true := by decide +kernel
theorem prefix_transition_333 : prefixTransitionCheck 333=true := by decide +kernel
theorem prefix_transition_334 : prefixTransitionCheck 334=true := by decide +kernel
theorem prefix_transition_335 : prefixTransitionCheck 335=true := by decide +kernel

theorem prefix_transitions_20 (i : ℕ) (hi0 : 320 ≤ i) (hi1 : i < 336) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_320
  · exact prefix_transition_321
  · exact prefix_transition_322
  · exact prefix_transition_323
  · exact prefix_transition_324
  · exact prefix_transition_325
  · exact prefix_transition_326
  · exact prefix_transition_327
  · exact prefix_transition_328
  · exact prefix_transition_329
  · exact prefix_transition_330
  · exact prefix_transition_331
  · exact prefix_transition_332
  · exact prefix_transition_333
  · exact prefix_transition_334
  · exact prefix_transition_335

#print axioms prefix_transitions_20
end Erdos7No9Certificate
