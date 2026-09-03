import Submission.No9CoverageChecks

/-! Kernel-certified coverage of the individual-prime prefix. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000

theorem prefix_prime_coverage_check : prefixPrimeCoverageCheck=true := by decide +kernel
#print axioms prefix_prime_coverage_check
end Erdos7No9Certificate
