import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_544 : prefixTransitionCheck 544=true := by decide +kernel
theorem prefix_transition_545 : prefixTransitionCheck 545=true := by decide +kernel
theorem prefix_transition_546 : prefixTransitionCheck 546=true := by decide +kernel
theorem prefix_transition_547 : prefixTransitionCheck 547=true := by decide +kernel
theorem prefix_transition_548 : prefixTransitionCheck 548=true := by decide +kernel
theorem prefix_transition_549 : prefixTransitionCheck 549=true := by decide +kernel
theorem prefix_transition_550 : prefixTransitionCheck 550=true := by decide +kernel
theorem prefix_transition_551 : prefixTransitionCheck 551=true := by decide +kernel
theorem prefix_transition_552 : prefixTransitionCheck 552=true := by decide +kernel
theorem prefix_transition_553 : prefixTransitionCheck 553=true := by decide +kernel
theorem prefix_transition_554 : prefixTransitionCheck 554=true := by decide +kernel
theorem prefix_transition_555 : prefixTransitionCheck 555=true := by decide +kernel
theorem prefix_transition_556 : prefixTransitionCheck 556=true := by decide +kernel
theorem prefix_transition_557 : prefixTransitionCheck 557=true := by decide +kernel
theorem prefix_transition_558 : prefixTransitionCheck 558=true := by decide +kernel
theorem prefix_transition_559 : prefixTransitionCheck 559=true := by decide +kernel

theorem prefix_transitions_34 (i : ℕ) (hi0 : 544 ≤ i) (hi1 : i < 560) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_544
  · exact prefix_transition_545
  · exact prefix_transition_546
  · exact prefix_transition_547
  · exact prefix_transition_548
  · exact prefix_transition_549
  · exact prefix_transition_550
  · exact prefix_transition_551
  · exact prefix_transition_552
  · exact prefix_transition_553
  · exact prefix_transition_554
  · exact prefix_transition_555
  · exact prefix_transition_556
  · exact prefix_transition_557
  · exact prefix_transition_558
  · exact prefix_transition_559

#print axioms prefix_transitions_34
end Erdos7No9Certificate
