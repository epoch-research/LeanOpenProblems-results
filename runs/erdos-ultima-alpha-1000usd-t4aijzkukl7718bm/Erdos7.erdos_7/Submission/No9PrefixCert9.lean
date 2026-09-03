import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_144 : prefixTransitionCheck 144=true := by decide +kernel
theorem prefix_transition_145 : prefixTransitionCheck 145=true := by decide +kernel
theorem prefix_transition_146 : prefixTransitionCheck 146=true := by decide +kernel
theorem prefix_transition_147 : prefixTransitionCheck 147=true := by decide +kernel
theorem prefix_transition_148 : prefixTransitionCheck 148=true := by decide +kernel
theorem prefix_transition_149 : prefixTransitionCheck 149=true := by decide +kernel
theorem prefix_transition_150 : prefixTransitionCheck 150=true := by decide +kernel
theorem prefix_transition_151 : prefixTransitionCheck 151=true := by decide +kernel
theorem prefix_transition_152 : prefixTransitionCheck 152=true := by decide +kernel
theorem prefix_transition_153 : prefixTransitionCheck 153=true := by decide +kernel
theorem prefix_transition_154 : prefixTransitionCheck 154=true := by decide +kernel
theorem prefix_transition_155 : prefixTransitionCheck 155=true := by decide +kernel
theorem prefix_transition_156 : prefixTransitionCheck 156=true := by decide +kernel
theorem prefix_transition_157 : prefixTransitionCheck 157=true := by decide +kernel
theorem prefix_transition_158 : prefixTransitionCheck 158=true := by decide +kernel
theorem prefix_transition_159 : prefixTransitionCheck 159=true := by decide +kernel

theorem prefix_transitions_9 (i : ℕ) (hi0 : 144 ≤ i) (hi1 : i < 160) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_144
  · exact prefix_transition_145
  · exact prefix_transition_146
  · exact prefix_transition_147
  · exact prefix_transition_148
  · exact prefix_transition_149
  · exact prefix_transition_150
  · exact prefix_transition_151
  · exact prefix_transition_152
  · exact prefix_transition_153
  · exact prefix_transition_154
  · exact prefix_transition_155
  · exact prefix_transition_156
  · exact prefix_transition_157
  · exact prefix_transition_158
  · exact prefix_transition_159

#print axioms prefix_transitions_9
end Erdos7No9Certificate
