import Submission.No9TransitionChecks

/-! Individual integer transitions checked by the kernel. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_transition_256 : blockTransitionCheck 256=true := by decide +kernel
theorem block_transition_257 : blockTransitionCheck 257=true := by decide +kernel
theorem block_transition_258 : blockTransitionCheck 258=true := by decide +kernel
theorem block_transition_259 : blockTransitionCheck 259=true := by decide +kernel
theorem block_transition_260 : blockTransitionCheck 260=true := by decide +kernel
theorem block_transition_261 : blockTransitionCheck 261=true := by decide +kernel
theorem block_transition_262 : blockTransitionCheck 262=true := by decide +kernel
theorem block_transition_263 : blockTransitionCheck 263=true := by decide +kernel
theorem block_transition_264 : blockTransitionCheck 264=true := by decide +kernel
theorem block_transition_265 : blockTransitionCheck 265=true := by decide +kernel
theorem block_transition_266 : blockTransitionCheck 266=true := by decide +kernel
theorem block_transition_267 : blockTransitionCheck 267=true := by decide +kernel
theorem block_transition_268 : blockTransitionCheck 268=true := by decide +kernel
theorem block_transition_269 : blockTransitionCheck 269=true := by decide +kernel
theorem block_transition_270 : blockTransitionCheck 270=true := by decide +kernel
theorem block_transition_271 : blockTransitionCheck 271=true := by decide +kernel

theorem block_transitions_16 (i : ℕ) (hi0 : 256 ≤ i) (hi1 : i < 272) : blockTransitionCheck i=true := by
  interval_cases i
  · exact block_transition_256
  · exact block_transition_257
  · exact block_transition_258
  · exact block_transition_259
  · exact block_transition_260
  · exact block_transition_261
  · exact block_transition_262
  · exact block_transition_263
  · exact block_transition_264
  · exact block_transition_265
  · exact block_transition_266
  · exact block_transition_267
  · exact block_transition_268
  · exact block_transition_269
  · exact block_transition_270
  · exact block_transition_271

#print axioms block_transitions_16
end Erdos7No9Certificate
