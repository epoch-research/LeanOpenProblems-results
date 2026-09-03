import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_416 : prefixTransitionCheck 416=true := by decide +kernel
theorem prefix_transition_417 : prefixTransitionCheck 417=true := by decide +kernel
theorem prefix_transition_418 : prefixTransitionCheck 418=true := by decide +kernel
theorem prefix_transition_419 : prefixTransitionCheck 419=true := by decide +kernel
theorem prefix_transition_420 : prefixTransitionCheck 420=true := by decide +kernel
theorem prefix_transition_421 : prefixTransitionCheck 421=true := by decide +kernel
theorem prefix_transition_422 : prefixTransitionCheck 422=true := by decide +kernel
theorem prefix_transition_423 : prefixTransitionCheck 423=true := by decide +kernel
theorem prefix_transition_424 : prefixTransitionCheck 424=true := by decide +kernel
theorem prefix_transition_425 : prefixTransitionCheck 425=true := by decide +kernel
theorem prefix_transition_426 : prefixTransitionCheck 426=true := by decide +kernel
theorem prefix_transition_427 : prefixTransitionCheck 427=true := by decide +kernel
theorem prefix_transition_428 : prefixTransitionCheck 428=true := by decide +kernel
theorem prefix_transition_429 : prefixTransitionCheck 429=true := by decide +kernel
theorem prefix_transition_430 : prefixTransitionCheck 430=true := by decide +kernel
theorem prefix_transition_431 : prefixTransitionCheck 431=true := by decide +kernel

theorem prefix_transitions_26 (i : ℕ) (hi0 : 416 ≤ i) (hi1 : i < 432) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_416
  · exact prefix_transition_417
  · exact prefix_transition_418
  · exact prefix_transition_419
  · exact prefix_transition_420
  · exact prefix_transition_421
  · exact prefix_transition_422
  · exact prefix_transition_423
  · exact prefix_transition_424
  · exact prefix_transition_425
  · exact prefix_transition_426
  · exact prefix_transition_427
  · exact prefix_transition_428
  · exact prefix_transition_429
  · exact prefix_transition_430
  · exact prefix_transition_431

#print axioms prefix_transitions_26
end Erdos7No9Certificate
