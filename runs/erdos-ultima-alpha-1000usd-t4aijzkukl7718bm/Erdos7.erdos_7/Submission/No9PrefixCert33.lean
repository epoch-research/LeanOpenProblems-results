import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_528 : prefixTransitionCheck 528=true := by decide +kernel
theorem prefix_transition_529 : prefixTransitionCheck 529=true := by decide +kernel
theorem prefix_transition_530 : prefixTransitionCheck 530=true := by decide +kernel
theorem prefix_transition_531 : prefixTransitionCheck 531=true := by decide +kernel
theorem prefix_transition_532 : prefixTransitionCheck 532=true := by decide +kernel
theorem prefix_transition_533 : prefixTransitionCheck 533=true := by decide +kernel
theorem prefix_transition_534 : prefixTransitionCheck 534=true := by decide +kernel
theorem prefix_transition_535 : prefixTransitionCheck 535=true := by decide +kernel
theorem prefix_transition_536 : prefixTransitionCheck 536=true := by decide +kernel
theorem prefix_transition_537 : prefixTransitionCheck 537=true := by decide +kernel
theorem prefix_transition_538 : prefixTransitionCheck 538=true := by decide +kernel
theorem prefix_transition_539 : prefixTransitionCheck 539=true := by decide +kernel
theorem prefix_transition_540 : prefixTransitionCheck 540=true := by decide +kernel
theorem prefix_transition_541 : prefixTransitionCheck 541=true := by decide +kernel
theorem prefix_transition_542 : prefixTransitionCheck 542=true := by decide +kernel
theorem prefix_transition_543 : prefixTransitionCheck 543=true := by decide +kernel

theorem prefix_transitions_33 (i : ℕ) (hi0 : 528 ≤ i) (hi1 : i < 544) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_528
  · exact prefix_transition_529
  · exact prefix_transition_530
  · exact prefix_transition_531
  · exact prefix_transition_532
  · exact prefix_transition_533
  · exact prefix_transition_534
  · exact prefix_transition_535
  · exact prefix_transition_536
  · exact prefix_transition_537
  · exact prefix_transition_538
  · exact prefix_transition_539
  · exact prefix_transition_540
  · exact prefix_transition_541
  · exact prefix_transition_542
  · exact prefix_transition_543

#print axioms prefix_transitions_33
end Erdos7No9Certificate
