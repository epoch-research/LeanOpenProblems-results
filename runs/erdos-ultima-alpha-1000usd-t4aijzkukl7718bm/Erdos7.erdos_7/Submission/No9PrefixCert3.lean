import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_48 : prefixTransitionCheck 48=true := by decide +kernel
theorem prefix_transition_49 : prefixTransitionCheck 49=true := by decide +kernel
theorem prefix_transition_50 : prefixTransitionCheck 50=true := by decide +kernel
theorem prefix_transition_51 : prefixTransitionCheck 51=true := by decide +kernel
theorem prefix_transition_52 : prefixTransitionCheck 52=true := by decide +kernel
theorem prefix_transition_53 : prefixTransitionCheck 53=true := by decide +kernel
theorem prefix_transition_54 : prefixTransitionCheck 54=true := by decide +kernel
theorem prefix_transition_55 : prefixTransitionCheck 55=true := by decide +kernel
theorem prefix_transition_56 : prefixTransitionCheck 56=true := by decide +kernel
theorem prefix_transition_57 : prefixTransitionCheck 57=true := by decide +kernel
theorem prefix_transition_58 : prefixTransitionCheck 58=true := by decide +kernel
theorem prefix_transition_59 : prefixTransitionCheck 59=true := by decide +kernel
theorem prefix_transition_60 : prefixTransitionCheck 60=true := by decide +kernel
theorem prefix_transition_61 : prefixTransitionCheck 61=true := by decide +kernel
theorem prefix_transition_62 : prefixTransitionCheck 62=true := by decide +kernel
theorem prefix_transition_63 : prefixTransitionCheck 63=true := by decide +kernel

theorem prefix_transitions_3 (i : ℕ) (hi0 : 48 ≤ i) (hi1 : i < 64) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_48
  · exact prefix_transition_49
  · exact prefix_transition_50
  · exact prefix_transition_51
  · exact prefix_transition_52
  · exact prefix_transition_53
  · exact prefix_transition_54
  · exact prefix_transition_55
  · exact prefix_transition_56
  · exact prefix_transition_57
  · exact prefix_transition_58
  · exact prefix_transition_59
  · exact prefix_transition_60
  · exact prefix_transition_61
  · exact prefix_transition_62
  · exact prefix_transition_63

#print axioms prefix_transitions_3
end Erdos7No9Certificate
