import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_64 : blockTransitionCheck 64=true := by decide +kernel
theorem block_transition_65 : blockTransitionCheck 65=true := by decide +kernel
theorem block_transition_66 : blockTransitionCheck 66=true := by decide +kernel
theorem block_transition_67 : blockTransitionCheck 67=true := by decide +kernel
theorem block_transition_68 : blockTransitionCheck 68=true := by decide +kernel
theorem block_transition_69 : blockTransitionCheck 69=true := by decide +kernel
theorem block_transition_70 : blockTransitionCheck 70=true := by decide +kernel
theorem block_transition_71 : blockTransitionCheck 71=true := by decide +kernel
theorem block_transition_72 : blockTransitionCheck 72=true := by decide +kernel
theorem block_transition_73 : blockTransitionCheck 73=true := by decide +kernel
theorem block_transition_74 : blockTransitionCheck 74=true := by decide +kernel
theorem block_transition_75 : blockTransitionCheck 75=true := by decide +kernel
theorem block_transition_76 : blockTransitionCheck 76=true := by decide +kernel
theorem block_transition_77 : blockTransitionCheck 77=true := by decide +kernel
theorem block_transition_78 : blockTransitionCheck 78=true := by decide +kernel
theorem block_transition_79 : blockTransitionCheck 79=true := by decide +kernel

theorem block_transitions_4 (i : ℕ) (hi0 : 64 ≤ i) (hi1 : i < 80) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_64
  · exact block_transition_65
  · exact block_transition_66
  · exact block_transition_67
  · exact block_transition_68
  · exact block_transition_69
  · exact block_transition_70
  · exact block_transition_71
  · exact block_transition_72
  · exact block_transition_73
  · exact block_transition_74
  · exact block_transition_75
  · exact block_transition_76
  · exact block_transition_77
  · exact block_transition_78
  · exact block_transition_79

#print axioms block_transitions_4
end Erdos7No9Certificate
