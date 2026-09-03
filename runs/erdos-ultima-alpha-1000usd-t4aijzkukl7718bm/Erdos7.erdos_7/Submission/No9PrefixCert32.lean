import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_512 : prefixTransitionCheck 512=true := by decide +kernel
theorem prefix_transition_513 : prefixTransitionCheck 513=true := by decide +kernel
theorem prefix_transition_514 : prefixTransitionCheck 514=true := by decide +kernel
theorem prefix_transition_515 : prefixTransitionCheck 515=true := by decide +kernel
theorem prefix_transition_516 : prefixTransitionCheck 516=true := by decide +kernel
theorem prefix_transition_517 : prefixTransitionCheck 517=true := by decide +kernel
theorem prefix_transition_518 : prefixTransitionCheck 518=true := by decide +kernel
theorem prefix_transition_519 : prefixTransitionCheck 519=true := by decide +kernel
theorem prefix_transition_520 : prefixTransitionCheck 520=true := by decide +kernel
theorem prefix_transition_521 : prefixTransitionCheck 521=true := by decide +kernel
theorem prefix_transition_522 : prefixTransitionCheck 522=true := by decide +kernel
theorem prefix_transition_523 : prefixTransitionCheck 523=true := by decide +kernel
theorem prefix_transition_524 : prefixTransitionCheck 524=true := by decide +kernel
theorem prefix_transition_525 : prefixTransitionCheck 525=true := by decide +kernel
theorem prefix_transition_526 : prefixTransitionCheck 526=true := by decide +kernel
theorem prefix_transition_527 : prefixTransitionCheck 527=true := by decide +kernel

theorem prefix_transitions_32 (i : ℕ) (hi0 : 512 ≤ i) (hi1 : i < 528) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_512
  · exact prefix_transition_513
  · exact prefix_transition_514
  · exact prefix_transition_515
  · exact prefix_transition_516
  · exact prefix_transition_517
  · exact prefix_transition_518
  · exact prefix_transition_519
  · exact prefix_transition_520
  · exact prefix_transition_521
  · exact prefix_transition_522
  · exact prefix_transition_523
  · exact prefix_transition_524
  · exact prefix_transition_525
  · exact prefix_transition_526
  · exact prefix_transition_527

#print axioms prefix_transitions_32
end Erdos7No9Certificate
