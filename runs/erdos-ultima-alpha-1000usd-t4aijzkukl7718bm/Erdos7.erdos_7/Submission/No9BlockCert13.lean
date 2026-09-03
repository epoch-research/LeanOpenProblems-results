import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_208 : blockTransitionCheck 208=true := by decide +kernel
theorem block_transition_209 : blockTransitionCheck 209=true := by decide +kernel
theorem block_transition_210 : blockTransitionCheck 210=true := by decide +kernel
theorem block_transition_211 : blockTransitionCheck 211=true := by decide +kernel
theorem block_transition_212 : blockTransitionCheck 212=true := by decide +kernel
theorem block_transition_213 : blockTransitionCheck 213=true := by decide +kernel
theorem block_transition_214 : blockTransitionCheck 214=true := by decide +kernel
theorem block_transition_215 : blockTransitionCheck 215=true := by decide +kernel
theorem block_transition_216 : blockTransitionCheck 216=true := by decide +kernel
theorem block_transition_217 : blockTransitionCheck 217=true := by decide +kernel
theorem block_transition_218 : blockTransitionCheck 218=true := by decide +kernel
theorem block_transition_219 : blockTransitionCheck 219=true := by decide +kernel
theorem block_transition_220 : blockTransitionCheck 220=true := by decide +kernel
theorem block_transition_221 : blockTransitionCheck 221=true := by decide +kernel
theorem block_transition_222 : blockTransitionCheck 222=true := by decide +kernel
theorem block_transition_223 : blockTransitionCheck 223=true := by decide +kernel

theorem block_transitions_13 (i : ℕ) (hi0 : 208 ≤ i) (hi1 : i < 224) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_208
  · exact block_transition_209
  · exact block_transition_210
  · exact block_transition_211
  · exact block_transition_212
  · exact block_transition_213
  · exact block_transition_214
  · exact block_transition_215
  · exact block_transition_216
  · exact block_transition_217
  · exact block_transition_218
  · exact block_transition_219
  · exact block_transition_220
  · exact block_transition_221
  · exact block_transition_222
  · exact block_transition_223

#print axioms block_transitions_13
end Erdos7No9Certificate
