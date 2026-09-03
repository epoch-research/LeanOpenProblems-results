import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_480 : prefixTransitionCheck 480=true := by decide +kernel
theorem prefix_transition_481 : prefixTransitionCheck 481=true := by decide +kernel
theorem prefix_transition_482 : prefixTransitionCheck 482=true := by decide +kernel
theorem prefix_transition_483 : prefixTransitionCheck 483=true := by decide +kernel
theorem prefix_transition_484 : prefixTransitionCheck 484=true := by decide +kernel
theorem prefix_transition_485 : prefixTransitionCheck 485=true := by decide +kernel
theorem prefix_transition_486 : prefixTransitionCheck 486=true := by decide +kernel
theorem prefix_transition_487 : prefixTransitionCheck 487=true := by decide +kernel
theorem prefix_transition_488 : prefixTransitionCheck 488=true := by decide +kernel
theorem prefix_transition_489 : prefixTransitionCheck 489=true := by decide +kernel
theorem prefix_transition_490 : prefixTransitionCheck 490=true := by decide +kernel
theorem prefix_transition_491 : prefixTransitionCheck 491=true := by decide +kernel
theorem prefix_transition_492 : prefixTransitionCheck 492=true := by decide +kernel
theorem prefix_transition_493 : prefixTransitionCheck 493=true := by decide +kernel
theorem prefix_transition_494 : prefixTransitionCheck 494=true := by decide +kernel
theorem prefix_transition_495 : prefixTransitionCheck 495=true := by decide +kernel

theorem prefix_transitions_30 (i : ℕ) (hi0 : 480 ≤ i) (hi1 : i < 496) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_480
  · exact prefix_transition_481
  · exact prefix_transition_482
  · exact prefix_transition_483
  · exact prefix_transition_484
  · exact prefix_transition_485
  · exact prefix_transition_486
  · exact prefix_transition_487
  · exact prefix_transition_488
  · exact prefix_transition_489
  · exact prefix_transition_490
  · exact prefix_transition_491
  · exact prefix_transition_492
  · exact prefix_transition_493
  · exact prefix_transition_494
  · exact prefix_transition_495

#print axioms prefix_transitions_30
end Erdos7No9Certificate
