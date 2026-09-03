import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_48 : blockTransitionCheck 48=true := by decide +kernel
theorem block_transition_49 : blockTransitionCheck 49=true := by decide +kernel
theorem block_transition_50 : blockTransitionCheck 50=true := by decide +kernel
theorem block_transition_51 : blockTransitionCheck 51=true := by decide +kernel
theorem block_transition_52 : blockTransitionCheck 52=true := by decide +kernel
theorem block_transition_53 : blockTransitionCheck 53=true := by decide +kernel
theorem block_transition_54 : blockTransitionCheck 54=true := by decide +kernel
theorem block_transition_55 : blockTransitionCheck 55=true := by decide +kernel
theorem block_transition_56 : blockTransitionCheck 56=true := by decide +kernel
theorem block_transition_57 : blockTransitionCheck 57=true := by decide +kernel
theorem block_transition_58 : blockTransitionCheck 58=true := by decide +kernel
theorem block_transition_59 : blockTransitionCheck 59=true := by decide +kernel
theorem block_transition_60 : blockTransitionCheck 60=true := by decide +kernel
theorem block_transition_61 : blockTransitionCheck 61=true := by decide +kernel
theorem block_transition_62 : blockTransitionCheck 62=true := by decide +kernel
theorem block_transition_63 : blockTransitionCheck 63=true := by decide +kernel

theorem block_transitions_3 (i : ℕ) (hi0 : 48 ≤ i) (hi1 : i < 64) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_48
  · exact block_transition_49
  · exact block_transition_50
  · exact block_transition_51
  · exact block_transition_52
  · exact block_transition_53
  · exact block_transition_54
  · exact block_transition_55
  · exact block_transition_56
  · exact block_transition_57
  · exact block_transition_58
  · exact block_transition_59
  · exact block_transition_60
  · exact block_transition_61
  · exact block_transition_62
  · exact block_transition_63

#print axioms block_transitions_3
end Erdos7No9Certificate
