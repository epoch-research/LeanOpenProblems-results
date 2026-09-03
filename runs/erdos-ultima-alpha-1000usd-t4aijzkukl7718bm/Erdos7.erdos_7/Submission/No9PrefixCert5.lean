import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_80 : prefixTransitionCheck 80=true := by decide +kernel
theorem prefix_transition_81 : prefixTransitionCheck 81=true := by decide +kernel
theorem prefix_transition_82 : prefixTransitionCheck 82=true := by decide +kernel
theorem prefix_transition_83 : prefixTransitionCheck 83=true := by decide +kernel
theorem prefix_transition_84 : prefixTransitionCheck 84=true := by decide +kernel
theorem prefix_transition_85 : prefixTransitionCheck 85=true := by decide +kernel
theorem prefix_transition_86 : prefixTransitionCheck 86=true := by decide +kernel
theorem prefix_transition_87 : prefixTransitionCheck 87=true := by decide +kernel
theorem prefix_transition_88 : prefixTransitionCheck 88=true := by decide +kernel
theorem prefix_transition_89 : prefixTransitionCheck 89=true := by decide +kernel
theorem prefix_transition_90 : prefixTransitionCheck 90=true := by decide +kernel
theorem prefix_transition_91 : prefixTransitionCheck 91=true := by decide +kernel
theorem prefix_transition_92 : prefixTransitionCheck 92=true := by decide +kernel
theorem prefix_transition_93 : prefixTransitionCheck 93=true := by decide +kernel
theorem prefix_transition_94 : prefixTransitionCheck 94=true := by decide +kernel
theorem prefix_transition_95 : prefixTransitionCheck 95=true := by decide +kernel

theorem prefix_transitions_5 (i : ℕ) (hi0 : 80 ≤ i) (hi1 : i < 96) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_80
  · exact prefix_transition_81
  · exact prefix_transition_82
  · exact prefix_transition_83
  · exact prefix_transition_84
  · exact prefix_transition_85
  · exact prefix_transition_86
  · exact prefix_transition_87
  · exact prefix_transition_88
  · exact prefix_transition_89
  · exact prefix_transition_90
  · exact prefix_transition_91
  · exact prefix_transition_92
  · exact prefix_transition_93
  · exact prefix_transition_94
  · exact prefix_transition_95

#print axioms prefix_transitions_5
end Erdos7No9Certificate
