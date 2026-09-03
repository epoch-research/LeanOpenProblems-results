import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_560 : prefixTransitionCheck 560=true := by decide +kernel
theorem prefix_transition_561 : prefixTransitionCheck 561=true := by decide +kernel
theorem prefix_transition_562 : prefixTransitionCheck 562=true := by decide +kernel
theorem prefix_transition_563 : prefixTransitionCheck 563=true := by decide +kernel
theorem prefix_transition_564 : prefixTransitionCheck 564=true := by decide +kernel
theorem prefix_transition_565 : prefixTransitionCheck 565=true := by decide +kernel
theorem prefix_transition_566 : prefixTransitionCheck 566=true := by decide +kernel
theorem prefix_transition_567 : prefixTransitionCheck 567=true := by decide +kernel
theorem prefix_transition_568 : prefixTransitionCheck 568=true := by decide +kernel
theorem prefix_transition_569 : prefixTransitionCheck 569=true := by decide +kernel
theorem prefix_transition_570 : prefixTransitionCheck 570=true := by decide +kernel
theorem prefix_transition_571 : prefixTransitionCheck 571=true := by decide +kernel
theorem prefix_transition_572 : prefixTransitionCheck 572=true := by decide +kernel
theorem prefix_transition_573 : prefixTransitionCheck 573=true := by decide +kernel
theorem prefix_transition_574 : prefixTransitionCheck 574=true := by decide +kernel
theorem prefix_transition_575 : prefixTransitionCheck 575=true := by decide +kernel

theorem prefix_transitions_35 (i : ℕ) (hi0 : 560 ≤ i) (hi1 : i < 576) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_560
  · exact prefix_transition_561
  · exact prefix_transition_562
  · exact prefix_transition_563
  · exact prefix_transition_564
  · exact prefix_transition_565
  · exact prefix_transition_566
  · exact prefix_transition_567
  · exact prefix_transition_568
  · exact prefix_transition_569
  · exact prefix_transition_570
  · exact prefix_transition_571
  · exact prefix_transition_572
  · exact prefix_transition_573
  · exact prefix_transition_574
  · exact prefix_transition_575

#print axioms prefix_transitions_35
end Erdos7No9Certificate
