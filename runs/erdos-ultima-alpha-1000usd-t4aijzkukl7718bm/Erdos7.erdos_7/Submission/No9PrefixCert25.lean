import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_400 : prefixTransitionCheck 400=true := by decide +kernel
theorem prefix_transition_401 : prefixTransitionCheck 401=true := by decide +kernel
theorem prefix_transition_402 : prefixTransitionCheck 402=true := by decide +kernel
theorem prefix_transition_403 : prefixTransitionCheck 403=true := by decide +kernel
theorem prefix_transition_404 : prefixTransitionCheck 404=true := by decide +kernel
theorem prefix_transition_405 : prefixTransitionCheck 405=true := by decide +kernel
theorem prefix_transition_406 : prefixTransitionCheck 406=true := by decide +kernel
theorem prefix_transition_407 : prefixTransitionCheck 407=true := by decide +kernel
theorem prefix_transition_408 : prefixTransitionCheck 408=true := by decide +kernel
theorem prefix_transition_409 : prefixTransitionCheck 409=true := by decide +kernel
theorem prefix_transition_410 : prefixTransitionCheck 410=true := by decide +kernel
theorem prefix_transition_411 : prefixTransitionCheck 411=true := by decide +kernel
theorem prefix_transition_412 : prefixTransitionCheck 412=true := by decide +kernel
theorem prefix_transition_413 : prefixTransitionCheck 413=true := by decide +kernel
theorem prefix_transition_414 : prefixTransitionCheck 414=true := by decide +kernel
theorem prefix_transition_415 : prefixTransitionCheck 415=true := by decide +kernel

theorem prefix_transitions_25 (i : ℕ) (hi0 : 400 ≤ i) (hi1 : i < 416) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_400
  · exact prefix_transition_401
  · exact prefix_transition_402
  · exact prefix_transition_403
  · exact prefix_transition_404
  · exact prefix_transition_405
  · exact prefix_transition_406
  · exact prefix_transition_407
  · exact prefix_transition_408
  · exact prefix_transition_409
  · exact prefix_transition_410
  · exact prefix_transition_411
  · exact prefix_transition_412
  · exact prefix_transition_413
  · exact prefix_transition_414
  · exact prefix_transition_415

#print axioms prefix_transitions_25
end Erdos7No9Certificate
