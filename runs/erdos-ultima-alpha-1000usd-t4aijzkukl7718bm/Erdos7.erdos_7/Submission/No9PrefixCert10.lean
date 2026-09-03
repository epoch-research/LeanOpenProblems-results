import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_160 : prefixTransitionCheck 160=true := by decide +kernel
theorem prefix_transition_161 : prefixTransitionCheck 161=true := by decide +kernel
theorem prefix_transition_162 : prefixTransitionCheck 162=true := by decide +kernel
theorem prefix_transition_163 : prefixTransitionCheck 163=true := by decide +kernel
theorem prefix_transition_164 : prefixTransitionCheck 164=true := by decide +kernel
theorem prefix_transition_165 : prefixTransitionCheck 165=true := by decide +kernel
theorem prefix_transition_166 : prefixTransitionCheck 166=true := by decide +kernel
theorem prefix_transition_167 : prefixTransitionCheck 167=true := by decide +kernel
theorem prefix_transition_168 : prefixTransitionCheck 168=true := by decide +kernel
theorem prefix_transition_169 : prefixTransitionCheck 169=true := by decide +kernel
theorem prefix_transition_170 : prefixTransitionCheck 170=true := by decide +kernel
theorem prefix_transition_171 : prefixTransitionCheck 171=true := by decide +kernel
theorem prefix_transition_172 : prefixTransitionCheck 172=true := by decide +kernel
theorem prefix_transition_173 : prefixTransitionCheck 173=true := by decide +kernel
theorem prefix_transition_174 : prefixTransitionCheck 174=true := by decide +kernel
theorem prefix_transition_175 : prefixTransitionCheck 175=true := by decide +kernel

theorem prefix_transitions_10 (i : ℕ) (hi0 : 160 ≤ i) (hi1 : i < 176) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_160
  · exact prefix_transition_161
  · exact prefix_transition_162
  · exact prefix_transition_163
  · exact prefix_transition_164
  · exact prefix_transition_165
  · exact prefix_transition_166
  · exact prefix_transition_167
  · exact prefix_transition_168
  · exact prefix_transition_169
  · exact prefix_transition_170
  · exact prefix_transition_171
  · exact prefix_transition_172
  · exact prefix_transition_173
  · exact prefix_transition_174
  · exact prefix_transition_175

#print axioms prefix_transitions_10
end Erdos7No9Certificate
