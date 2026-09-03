import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_32 : prefixTransitionCheck 32=true := by decide +kernel
theorem prefix_transition_33 : prefixTransitionCheck 33=true := by decide +kernel
theorem prefix_transition_34 : prefixTransitionCheck 34=true := by decide +kernel
theorem prefix_transition_35 : prefixTransitionCheck 35=true := by decide +kernel
theorem prefix_transition_36 : prefixTransitionCheck 36=true := by decide +kernel
theorem prefix_transition_37 : prefixTransitionCheck 37=true := by decide +kernel
theorem prefix_transition_38 : prefixTransitionCheck 38=true := by decide +kernel
theorem prefix_transition_39 : prefixTransitionCheck 39=true := by decide +kernel
theorem prefix_transition_40 : prefixTransitionCheck 40=true := by decide +kernel
theorem prefix_transition_41 : prefixTransitionCheck 41=true := by decide +kernel
theorem prefix_transition_42 : prefixTransitionCheck 42=true := by decide +kernel
theorem prefix_transition_43 : prefixTransitionCheck 43=true := by decide +kernel
theorem prefix_transition_44 : prefixTransitionCheck 44=true := by decide +kernel
theorem prefix_transition_45 : prefixTransitionCheck 45=true := by decide +kernel
theorem prefix_transition_46 : prefixTransitionCheck 46=true := by decide +kernel
theorem prefix_transition_47 : prefixTransitionCheck 47=true := by decide +kernel

theorem prefix_transitions_2 (i : ℕ) (hi0 : 32 ≤ i) (hi1 : i < 48) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_32
  · exact prefix_transition_33
  · exact prefix_transition_34
  · exact prefix_transition_35
  · exact prefix_transition_36
  · exact prefix_transition_37
  · exact prefix_transition_38
  · exact prefix_transition_39
  · exact prefix_transition_40
  · exact prefix_transition_41
  · exact prefix_transition_42
  · exact prefix_transition_43
  · exact prefix_transition_44
  · exact prefix_transition_45
  · exact prefix_transition_46
  · exact prefix_transition_47

#print axioms prefix_transitions_2
end Erdos7No9Certificate
