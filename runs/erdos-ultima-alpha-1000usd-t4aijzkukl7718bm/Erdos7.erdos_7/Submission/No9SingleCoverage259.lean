import Submission.No9CoverageChecks

/-! One interval coverage check, isolated to bound kernel memory use. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000

theorem block_prime_coverage_259 : blockPrimeCoverageCheck 259=true := by decide +kernel
#print axioms block_prime_coverage_259
end Erdos7No9Certificate
