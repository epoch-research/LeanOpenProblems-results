import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_0 : blockPrimeCoverageCheck 0=true := by decide +kernel
theorem block_prime_coverage_1 : blockPrimeCoverageCheck 1=true := by decide +kernel
theorem block_prime_coverage_2 : blockPrimeCoverageCheck 2=true := by decide +kernel
theorem block_prime_coverage_3 : blockPrimeCoverageCheck 3=true := by decide +kernel
theorem block_prime_coverage_4 : blockPrimeCoverageCheck 4=true := by decide +kernel
theorem block_prime_coverage_5 : blockPrimeCoverageCheck 5=true := by decide +kernel
theorem block_prime_coverage_6 : blockPrimeCoverageCheck 6=true := by decide +kernel
theorem block_prime_coverage_7 : blockPrimeCoverageCheck 7=true := by decide +kernel
theorem block_prime_coverage_8 : blockPrimeCoverageCheck 8=true := by decide +kernel
theorem block_prime_coverage_9 : blockPrimeCoverageCheck 9=true := by decide +kernel
theorem block_prime_coverage_10 : blockPrimeCoverageCheck 10=true := by decide +kernel
theorem block_prime_coverage_11 : blockPrimeCoverageCheck 11=true := by decide +kernel
theorem block_prime_coverage_12 : blockPrimeCoverageCheck 12=true := by decide +kernel
theorem block_prime_coverage_13 : blockPrimeCoverageCheck 13=true := by decide +kernel
theorem block_prime_coverage_14 : blockPrimeCoverageCheck 14=true := by decide +kernel
theorem block_prime_coverage_15 : blockPrimeCoverageCheck 15=true := by decide +kernel

theorem block_prime_coverages_0 (i : ℕ) (hi0 : 0 ≤ i) (hi1 : i < 16) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_0
  · exact block_prime_coverage_1
  · exact block_prime_coverage_2
  · exact block_prime_coverage_3
  · exact block_prime_coverage_4
  · exact block_prime_coverage_5
  · exact block_prime_coverage_6
  · exact block_prime_coverage_7
  · exact block_prime_coverage_8
  · exact block_prime_coverage_9
  · exact block_prime_coverage_10
  · exact block_prime_coverage_11
  · exact block_prime_coverage_12
  · exact block_prime_coverage_13
  · exact block_prime_coverage_14
  · exact block_prime_coverage_15

#print axioms block_prime_coverages_0
end Erdos7No9Certificate
