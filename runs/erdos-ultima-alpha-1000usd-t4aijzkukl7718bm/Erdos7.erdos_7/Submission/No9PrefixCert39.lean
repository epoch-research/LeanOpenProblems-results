import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_624 : prefixTransitionCheck 624=true := by decide +kernel
theorem prefix_transition_625 : prefixTransitionCheck 625=true := by decide +kernel
theorem prefix_transition_626 : prefixTransitionCheck 626=true := by decide +kernel
theorem prefix_transition_627 : prefixTransitionCheck 627=true := by decide +kernel
theorem prefix_transition_628 : prefixTransitionCheck 628=true := by decide +kernel
theorem prefix_transition_629 : prefixTransitionCheck 629=true := by decide +kernel
theorem prefix_transition_630 : prefixTransitionCheck 630=true := by decide +kernel
theorem prefix_transition_631 : prefixTransitionCheck 631=true := by decide +kernel
theorem prefix_transition_632 : prefixTransitionCheck 632=true := by decide +kernel
theorem prefix_transition_633 : prefixTransitionCheck 633=true := by decide +kernel
theorem prefix_transition_634 : prefixTransitionCheck 634=true := by decide +kernel
theorem prefix_transition_635 : prefixTransitionCheck 635=true := by decide +kernel
theorem prefix_transition_636 : prefixTransitionCheck 636=true := by decide +kernel
theorem prefix_transition_637 : prefixTransitionCheck 637=true := by decide +kernel
theorem prefix_transition_638 : prefixTransitionCheck 638=true := by decide +kernel
theorem prefix_transition_639 : prefixTransitionCheck 639=true := by decide +kernel

theorem prefix_transitions_39 (i : ℕ) (hi0 : 624 ≤ i) (hi1 : i < 640) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_624
  · exact prefix_transition_625
  · exact prefix_transition_626
  · exact prefix_transition_627
  · exact prefix_transition_628
  · exact prefix_transition_629
  · exact prefix_transition_630
  · exact prefix_transition_631
  · exact prefix_transition_632
  · exact prefix_transition_633
  · exact prefix_transition_634
  · exact prefix_transition_635
  · exact prefix_transition_636
  · exact prefix_transition_637
  · exact prefix_transition_638
  · exact prefix_transition_639

#print axioms prefix_transitions_39
end Erdos7No9Certificate
