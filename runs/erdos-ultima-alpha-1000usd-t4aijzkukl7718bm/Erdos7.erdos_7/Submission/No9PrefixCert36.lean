import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_576 : prefixTransitionCheck 576=true := by decide +kernel
theorem prefix_transition_577 : prefixTransitionCheck 577=true := by decide +kernel
theorem prefix_transition_578 : prefixTransitionCheck 578=true := by decide +kernel
theorem prefix_transition_579 : prefixTransitionCheck 579=true := by decide +kernel
theorem prefix_transition_580 : prefixTransitionCheck 580=true := by decide +kernel
theorem prefix_transition_581 : prefixTransitionCheck 581=true := by decide +kernel
theorem prefix_transition_582 : prefixTransitionCheck 582=true := by decide +kernel
theorem prefix_transition_583 : prefixTransitionCheck 583=true := by decide +kernel
theorem prefix_transition_584 : prefixTransitionCheck 584=true := by decide +kernel
theorem prefix_transition_585 : prefixTransitionCheck 585=true := by decide +kernel
theorem prefix_transition_586 : prefixTransitionCheck 586=true := by decide +kernel
theorem prefix_transition_587 : prefixTransitionCheck 587=true := by decide +kernel
theorem prefix_transition_588 : prefixTransitionCheck 588=true := by decide +kernel
theorem prefix_transition_589 : prefixTransitionCheck 589=true := by decide +kernel
theorem prefix_transition_590 : prefixTransitionCheck 590=true := by decide +kernel
theorem prefix_transition_591 : prefixTransitionCheck 591=true := by decide +kernel

theorem prefix_transitions_36 (i : ℕ) (hi0 : 576 ≤ i) (hi1 : i < 592) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_576
  · exact prefix_transition_577
  · exact prefix_transition_578
  · exact prefix_transition_579
  · exact prefix_transition_580
  · exact prefix_transition_581
  · exact prefix_transition_582
  · exact prefix_transition_583
  · exact prefix_transition_584
  · exact prefix_transition_585
  · exact prefix_transition_586
  · exact prefix_transition_587
  · exact prefix_transition_588
  · exact prefix_transition_589
  · exact prefix_transition_590
  · exact prefix_transition_591

#print axioms prefix_transitions_36
end Erdos7No9Certificate
