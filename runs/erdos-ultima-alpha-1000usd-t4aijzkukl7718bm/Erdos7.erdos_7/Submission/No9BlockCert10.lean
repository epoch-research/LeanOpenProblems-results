import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_160 : blockTransitionCheck 160=true := by decide +kernel
theorem block_transition_161 : blockTransitionCheck 161=true := by decide +kernel
theorem block_transition_162 : blockTransitionCheck 162=true := by decide +kernel
theorem block_transition_163 : blockTransitionCheck 163=true := by decide +kernel
theorem block_transition_164 : blockTransitionCheck 164=true := by decide +kernel
theorem block_transition_165 : blockTransitionCheck 165=true := by decide +kernel
theorem block_transition_166 : blockTransitionCheck 166=true := by decide +kernel
theorem block_transition_167 : blockTransitionCheck 167=true := by decide +kernel
theorem block_transition_168 : blockTransitionCheck 168=true := by decide +kernel
theorem block_transition_169 : blockTransitionCheck 169=true := by decide +kernel
theorem block_transition_170 : blockTransitionCheck 170=true := by decide +kernel
theorem block_transition_171 : blockTransitionCheck 171=true := by decide +kernel
theorem block_transition_172 : blockTransitionCheck 172=true := by decide +kernel
theorem block_transition_173 : blockTransitionCheck 173=true := by decide +kernel
theorem block_transition_174 : blockTransitionCheck 174=true := by decide +kernel
theorem block_transition_175 : blockTransitionCheck 175=true := by decide +kernel

theorem block_transitions_10 (i : ℕ) (hi0 : 160 ≤ i) (hi1 : i < 176) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_160
  · exact block_transition_161
  · exact block_transition_162
  · exact block_transition_163
  · exact block_transition_164
  · exact block_transition_165
  · exact block_transition_166
  · exact block_transition_167
  · exact block_transition_168
  · exact block_transition_169
  · exact block_transition_170
  · exact block_transition_171
  · exact block_transition_172
  · exact block_transition_173
  · exact block_transition_174
  · exact block_transition_175

#print axioms block_transitions_10
end Erdos7No9Certificate
