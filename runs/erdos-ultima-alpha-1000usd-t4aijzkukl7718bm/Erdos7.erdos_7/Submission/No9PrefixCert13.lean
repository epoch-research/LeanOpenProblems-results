import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem prefix_transition_208 : prefixTransitionCheck 208=true := by decide +kernel
theorem prefix_transition_209 : prefixTransitionCheck 209=true := by decide +kernel
theorem prefix_transition_210 : prefixTransitionCheck 210=true := by decide +kernel
theorem prefix_transition_211 : prefixTransitionCheck 211=true := by decide +kernel
theorem prefix_transition_212 : prefixTransitionCheck 212=true := by decide +kernel
theorem prefix_transition_213 : prefixTransitionCheck 213=true := by decide +kernel
theorem prefix_transition_214 : prefixTransitionCheck 214=true := by decide +kernel
theorem prefix_transition_215 : prefixTransitionCheck 215=true := by decide +kernel
theorem prefix_transition_216 : prefixTransitionCheck 216=true := by decide +kernel
theorem prefix_transition_217 : prefixTransitionCheck 217=true := by decide +kernel
theorem prefix_transition_218 : prefixTransitionCheck 218=true := by decide +kernel
theorem prefix_transition_219 : prefixTransitionCheck 219=true := by decide +kernel
theorem prefix_transition_220 : prefixTransitionCheck 220=true := by decide +kernel
theorem prefix_transition_221 : prefixTransitionCheck 221=true := by decide +kernel
theorem prefix_transition_222 : prefixTransitionCheck 222=true := by decide +kernel
theorem prefix_transition_223 : prefixTransitionCheck 223=true := by decide +kernel

theorem prefix_transitions_13 (i : ℕ) (hi0 : 208 ≤ i) (hi1 : i < 224) : prefixTransitionCheck i=true := by
  interval_cases i
  · exact prefix_transition_208
  · exact prefix_transition_209
  · exact prefix_transition_210
  · exact prefix_transition_211
  · exact prefix_transition_212
  · exact prefix_transition_213
  · exact prefix_transition_214
  · exact prefix_transition_215
  · exact prefix_transition_216
  · exact prefix_transition_217
  · exact prefix_transition_218
  · exact prefix_transition_219
  · exact prefix_transition_220
  · exact prefix_transition_221
  · exact prefix_transition_222
  · exact prefix_transition_223

#print axioms prefix_transitions_13
end Erdos7No9Certificate
