import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_80 : blockTransitionCheck 80=true := by decide +kernel
theorem block_transition_81 : blockTransitionCheck 81=true := by decide +kernel
theorem block_transition_82 : blockTransitionCheck 82=true := by decide +kernel
theorem block_transition_83 : blockTransitionCheck 83=true := by decide +kernel
theorem block_transition_84 : blockTransitionCheck 84=true := by decide +kernel
theorem block_transition_85 : blockTransitionCheck 85=true := by decide +kernel
theorem block_transition_86 : blockTransitionCheck 86=true := by decide +kernel
theorem block_transition_87 : blockTransitionCheck 87=true := by decide +kernel
theorem block_transition_88 : blockTransitionCheck 88=true := by decide +kernel
theorem block_transition_89 : blockTransitionCheck 89=true := by decide +kernel
theorem block_transition_90 : blockTransitionCheck 90=true := by decide +kernel
theorem block_transition_91 : blockTransitionCheck 91=true := by decide +kernel
theorem block_transition_92 : blockTransitionCheck 92=true := by decide +kernel
theorem block_transition_93 : blockTransitionCheck 93=true := by decide +kernel
theorem block_transition_94 : blockTransitionCheck 94=true := by decide +kernel
theorem block_transition_95 : blockTransitionCheck 95=true := by decide +kernel

theorem block_transitions_5 (i : ℕ) (hi0 : 80 ≤ i) (hi1 : i < 96) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_80
  · exact block_transition_81
  · exact block_transition_82
  · exact block_transition_83
  · exact block_transition_84
  · exact block_transition_85
  · exact block_transition_86
  · exact block_transition_87
  · exact block_transition_88
  · exact block_transition_89
  · exact block_transition_90
  · exact block_transition_91
  · exact block_transition_92
  · exact block_transition_93
  · exact block_transition_94
  · exact block_transition_95

#print axioms block_transitions_5
end Erdos7No9Certificate
