import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_32 : blockTransitionCheck 32=true := by decide +kernel
theorem block_transition_33 : blockTransitionCheck 33=true := by decide +kernel
theorem block_transition_34 : blockTransitionCheck 34=true := by decide +kernel
theorem block_transition_35 : blockTransitionCheck 35=true := by decide +kernel
theorem block_transition_36 : blockTransitionCheck 36=true := by decide +kernel
theorem block_transition_37 : blockTransitionCheck 37=true := by decide +kernel
theorem block_transition_38 : blockTransitionCheck 38=true := by decide +kernel
theorem block_transition_39 : blockTransitionCheck 39=true := by decide +kernel
theorem block_transition_40 : blockTransitionCheck 40=true := by decide +kernel
theorem block_transition_41 : blockTransitionCheck 41=true := by decide +kernel
theorem block_transition_42 : blockTransitionCheck 42=true := by decide +kernel
theorem block_transition_43 : blockTransitionCheck 43=true := by decide +kernel
theorem block_transition_44 : blockTransitionCheck 44=true := by decide +kernel
theorem block_transition_45 : blockTransitionCheck 45=true := by decide +kernel
theorem block_transition_46 : blockTransitionCheck 46=true := by decide +kernel
theorem block_transition_47 : blockTransitionCheck 47=true := by decide +kernel

theorem block_transitions_2 (i : ℕ) (hi0 : 32 ≤ i) (hi1 : i < 48) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_32
  · exact block_transition_33
  · exact block_transition_34
  · exact block_transition_35
  · exact block_transition_36
  · exact block_transition_37
  · exact block_transition_38
  · exact block_transition_39
  · exact block_transition_40
  · exact block_transition_41
  · exact block_transition_42
  · exact block_transition_43
  · exact block_transition_44
  · exact block_transition_45
  · exact block_transition_46
  · exact block_transition_47

#print axioms block_transitions_2
end Erdos7No9Certificate
