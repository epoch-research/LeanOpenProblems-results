import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_464 : prefixTransitionCheck 464=true := by decide +kernel
theorem prefix_transition_465 : prefixTransitionCheck 465=true := by decide +kernel
theorem prefix_transition_466 : prefixTransitionCheck 466=true := by decide +kernel
theorem prefix_transition_467 : prefixTransitionCheck 467=true := by decide +kernel
theorem prefix_transition_468 : prefixTransitionCheck 468=true := by decide +kernel
theorem prefix_transition_469 : prefixTransitionCheck 469=true := by decide +kernel
theorem prefix_transition_470 : prefixTransitionCheck 470=true := by decide +kernel
theorem prefix_transition_471 : prefixTransitionCheck 471=true := by decide +kernel
theorem prefix_transition_472 : prefixTransitionCheck 472=true := by decide +kernel
theorem prefix_transition_473 : prefixTransitionCheck 473=true := by decide +kernel
theorem prefix_transition_474 : prefixTransitionCheck 474=true := by decide +kernel
theorem prefix_transition_475 : prefixTransitionCheck 475=true := by decide +kernel
theorem prefix_transition_476 : prefixTransitionCheck 476=true := by decide +kernel
theorem prefix_transition_477 : prefixTransitionCheck 477=true := by decide +kernel
theorem prefix_transition_478 : prefixTransitionCheck 478=true := by decide +kernel
theorem prefix_transition_479 : prefixTransitionCheck 479=true := by decide +kernel

theorem prefix_transitions_29 (i : ℕ) (hi0 : 464 ≤ i) (hi1 : i < 480) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_464
  · exact prefix_transition_465
  · exact prefix_transition_466
  · exact prefix_transition_467
  · exact prefix_transition_468
  · exact prefix_transition_469
  · exact prefix_transition_470
  · exact prefix_transition_471
  · exact prefix_transition_472
  · exact prefix_transition_473
  · exact prefix_transition_474
  · exact prefix_transition_475
  · exact prefix_transition_476
  · exact prefix_transition_477
  · exact prefix_transition_478
  · exact prefix_transition_479

#print axioms prefix_transitions_29
end Erdos7No9Certificate
