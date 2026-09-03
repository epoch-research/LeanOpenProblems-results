import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_96 : prefixTransitionCheck 96=true := by decide +kernel
theorem prefix_transition_97 : prefixTransitionCheck 97=true := by decide +kernel
theorem prefix_transition_98 : prefixTransitionCheck 98=true := by decide +kernel
theorem prefix_transition_99 : prefixTransitionCheck 99=true := by decide +kernel
theorem prefix_transition_100 : prefixTransitionCheck 100=true := by decide +kernel
theorem prefix_transition_101 : prefixTransitionCheck 101=true := by decide +kernel
theorem prefix_transition_102 : prefixTransitionCheck 102=true := by decide +kernel
theorem prefix_transition_103 : prefixTransitionCheck 103=true := by decide +kernel
theorem prefix_transition_104 : prefixTransitionCheck 104=true := by decide +kernel
theorem prefix_transition_105 : prefixTransitionCheck 105=true := by decide +kernel
theorem prefix_transition_106 : prefixTransitionCheck 106=true := by decide +kernel
theorem prefix_transition_107 : prefixTransitionCheck 107=true := by decide +kernel
theorem prefix_transition_108 : prefixTransitionCheck 108=true := by decide +kernel
theorem prefix_transition_109 : prefixTransitionCheck 109=true := by decide +kernel
theorem prefix_transition_110 : prefixTransitionCheck 110=true := by decide +kernel
theorem prefix_transition_111 : prefixTransitionCheck 111=true := by decide +kernel

theorem prefix_transitions_6 (i : ℕ) (hi0 : 96 ≤ i) (hi1 : i < 112) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_96
  · exact prefix_transition_97
  · exact prefix_transition_98
  · exact prefix_transition_99
  · exact prefix_transition_100
  · exact prefix_transition_101
  · exact prefix_transition_102
  · exact prefix_transition_103
  · exact prefix_transition_104
  · exact prefix_transition_105
  · exact prefix_transition_106
  · exact prefix_transition_107
  · exact prefix_transition_108
  · exact prefix_transition_109
  · exact prefix_transition_110
  · exact prefix_transition_111

#print axioms prefix_transitions_6
end Erdos7No9Certificate
