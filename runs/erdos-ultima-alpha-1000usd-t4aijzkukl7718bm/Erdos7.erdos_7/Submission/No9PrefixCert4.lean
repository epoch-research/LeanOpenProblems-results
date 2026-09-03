import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_64 : prefixTransitionCheck 64=true := by decide +kernel
theorem prefix_transition_65 : prefixTransitionCheck 65=true := by decide +kernel
theorem prefix_transition_66 : prefixTransitionCheck 66=true := by decide +kernel
theorem prefix_transition_67 : prefixTransitionCheck 67=true := by decide +kernel
theorem prefix_transition_68 : prefixTransitionCheck 68=true := by decide +kernel
theorem prefix_transition_69 : prefixTransitionCheck 69=true := by decide +kernel
theorem prefix_transition_70 : prefixTransitionCheck 70=true := by decide +kernel
theorem prefix_transition_71 : prefixTransitionCheck 71=true := by decide +kernel
theorem prefix_transition_72 : prefixTransitionCheck 72=true := by decide +kernel
theorem prefix_transition_73 : prefixTransitionCheck 73=true := by decide +kernel
theorem prefix_transition_74 : prefixTransitionCheck 74=true := by decide +kernel
theorem prefix_transition_75 : prefixTransitionCheck 75=true := by decide +kernel
theorem prefix_transition_76 : prefixTransitionCheck 76=true := by decide +kernel
theorem prefix_transition_77 : prefixTransitionCheck 77=true := by decide +kernel
theorem prefix_transition_78 : prefixTransitionCheck 78=true := by decide +kernel
theorem prefix_transition_79 : prefixTransitionCheck 79=true := by decide +kernel

theorem prefix_transitions_4 (i : ℕ) (hi0 : 64 ≤ i) (hi1 : i < 80) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_64
  · exact prefix_transition_65
  · exact prefix_transition_66
  · exact prefix_transition_67
  · exact prefix_transition_68
  · exact prefix_transition_69
  · exact prefix_transition_70
  · exact prefix_transition_71
  · exact prefix_transition_72
  · exact prefix_transition_73
  · exact prefix_transition_74
  · exact prefix_transition_75
  · exact prefix_transition_76
  · exact prefix_transition_77
  · exact prefix_transition_78
  · exact prefix_transition_79

#print axioms prefix_transitions_4
end Erdos7No9Certificate
