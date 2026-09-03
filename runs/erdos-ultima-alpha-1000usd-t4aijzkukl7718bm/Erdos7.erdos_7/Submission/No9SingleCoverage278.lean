import Submission.No9CoverageChecks

/-! One interval coverage check, isolated to bound kernel memory use. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000

theorem block_prime_coverage_278 : blockPrimeCoverageCheck 278=true := by decide +kernel
#print axioms block_prime_coverage_278
end Erdos7No9Certificate
