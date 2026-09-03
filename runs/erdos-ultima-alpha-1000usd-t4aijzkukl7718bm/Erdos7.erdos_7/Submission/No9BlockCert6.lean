import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_96 : blockTransitionCheck 96=true := by decide +kernel
theorem block_transition_97 : blockTransitionCheck 97=true := by decide +kernel
theorem block_transition_98 : blockTransitionCheck 98=true := by decide +kernel
theorem block_transition_99 : blockTransitionCheck 99=true := by decide +kernel
theorem block_transition_100 : blockTransitionCheck 100=true := by decide +kernel
theorem block_transition_101 : blockTransitionCheck 101=true := by decide +kernel
theorem block_transition_102 : blockTransitionCheck 102=true := by decide +kernel
theorem block_transition_103 : blockTransitionCheck 103=true := by decide +kernel
theorem block_transition_104 : blockTransitionCheck 104=true := by decide +kernel
theorem block_transition_105 : blockTransitionCheck 105=true := by decide +kernel
theorem block_transition_106 : blockTransitionCheck 106=true := by decide +kernel
theorem block_transition_107 : blockTransitionCheck 107=true := by decide +kernel
theorem block_transition_108 : blockTransitionCheck 108=true := by decide +kernel
theorem block_transition_109 : blockTransitionCheck 109=true := by decide +kernel
theorem block_transition_110 : blockTransitionCheck 110=true := by decide +kernel
theorem block_transition_111 : blockTransitionCheck 111=true := by decide +kernel

theorem block_transitions_6 (i : ℕ) (hi0 : 96 ≤ i) (hi1 : i < 112) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_96
  · exact block_transition_97
  · exact block_transition_98
  · exact block_transition_99
  · exact block_transition_100
  · exact block_transition_101
  · exact block_transition_102
  · exact block_transition_103
  · exact block_transition_104
  · exact block_transition_105
  · exact block_transition_106
  · exact block_transition_107
  · exact block_transition_108
  · exact block_transition_109
  · exact block_transition_110
  · exact block_transition_111

#print axioms block_transitions_6
end Erdos7No9Certificate
