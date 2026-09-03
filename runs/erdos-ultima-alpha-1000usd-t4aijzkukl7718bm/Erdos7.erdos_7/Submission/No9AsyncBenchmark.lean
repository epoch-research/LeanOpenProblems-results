import Submission.No9CoverageChecks

/-! Sequential kernel-checking benchmark for a future standalone source. -/
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
namespace Erdos7No9Certificate

theorem async_285 : blockPrimeCoverageCheck 285=true := by decide +kernel
theorem async_286 : blockPrimeCoverageCheck 286=true := by decide +kernel
theorem async_287 : blockPrimeCoverageCheck 287=true := by decide +kernel
#print axioms async_287
end Erdos7No9Certificate
