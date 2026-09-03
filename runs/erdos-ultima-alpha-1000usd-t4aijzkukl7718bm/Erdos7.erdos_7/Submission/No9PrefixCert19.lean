import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_304 : prefixTransitionCheck 304=true := by decide +kernel
theorem prefix_transition_305 : prefixTransitionCheck 305=true := by decide +kernel
theorem prefix_transition_306 : prefixTransitionCheck 306=true := by decide +kernel
theorem prefix_transition_307 : prefixTransitionCheck 307=true := by decide +kernel
theorem prefix_transition_308 : prefixTransitionCheck 308=true := by decide +kernel
theorem prefix_transition_309 : prefixTransitionCheck 309=true := by decide +kernel
theorem prefix_transition_310 : prefixTransitionCheck 310=true := by decide +kernel
theorem prefix_transition_311 : prefixTransitionCheck 311=true := by decide +kernel
theorem prefix_transition_312 : prefixTransitionCheck 312=true := by decide +kernel
theorem prefix_transition_313 : prefixTransitionCheck 313=true := by decide +kernel
theorem prefix_transition_314 : prefixTransitionCheck 314=true := by decide +kernel
theorem prefix_transition_315 : prefixTransitionCheck 315=true := by decide +kernel
theorem prefix_transition_316 : prefixTransitionCheck 316=true := by decide +kernel
theorem prefix_transition_317 : prefixTransitionCheck 317=true := by decide +kernel
theorem prefix_transition_318 : prefixTransitionCheck 318=true := by decide +kernel
theorem prefix_transition_319 : prefixTransitionCheck 319=true := by decide +kernel

theorem prefix_transitions_19 (i : ℕ) (hi0 : 304 ≤ i) (hi1 : i < 320) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_304
  · exact prefix_transition_305
  · exact prefix_transition_306
  · exact prefix_transition_307
  · exact prefix_transition_308
  · exact prefix_transition_309
  · exact prefix_transition_310
  · exact prefix_transition_311
  · exact prefix_transition_312
  · exact prefix_transition_313
  · exact prefix_transition_314
  · exact prefix_transition_315
  · exact prefix_transition_316
  · exact prefix_transition_317
  · exact prefix_transition_318
  · exact prefix_transition_319

#print axioms prefix_transitions_19
end Erdos7No9Certificate
