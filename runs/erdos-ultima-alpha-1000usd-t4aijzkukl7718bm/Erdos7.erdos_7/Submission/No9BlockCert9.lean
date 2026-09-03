import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_144 : blockTransitionCheck 144=true := by decide +kernel
theorem block_transition_145 : blockTransitionCheck 145=true := by decide +kernel
theorem block_transition_146 : blockTransitionCheck 146=true := by decide +kernel
theorem block_transition_147 : blockTransitionCheck 147=true := by decide +kernel
theorem block_transition_148 : blockTransitionCheck 148=true := by decide +kernel
theorem block_transition_149 : blockTransitionCheck 149=true := by decide +kernel
theorem block_transition_150 : blockTransitionCheck 150=true := by decide +kernel
theorem block_transition_151 : blockTransitionCheck 151=true := by decide +kernel
theorem block_transition_152 : blockTransitionCheck 152=true := by decide +kernel
theorem block_transition_153 : blockTransitionCheck 153=true := by decide +kernel
theorem block_transition_154 : blockTransitionCheck 154=true := by decide +kernel
theorem block_transition_155 : blockTransitionCheck 155=true := by decide +kernel
theorem block_transition_156 : blockTransitionCheck 156=true := by decide +kernel
theorem block_transition_157 : blockTransitionCheck 157=true := by decide +kernel
theorem block_transition_158 : blockTransitionCheck 158=true := by decide +kernel
theorem block_transition_159 : blockTransitionCheck 159=true := by decide +kernel

theorem block_transitions_9 (i : ℕ) (hi0 : 144 ≤ i) (hi1 : i < 160) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_144
  · exact block_transition_145
  · exact block_transition_146
  · exact block_transition_147
  · exact block_transition_148
  · exact block_transition_149
  · exact block_transition_150
  · exact block_transition_151
  · exact block_transition_152
  · exact block_transition_153
  · exact block_transition_154
  · exact block_transition_155
  · exact block_transition_156
  · exact block_transition_157
  · exact block_transition_158
  · exact block_transition_159

#print axioms block_transitions_9
end Erdos7No9Certificate
