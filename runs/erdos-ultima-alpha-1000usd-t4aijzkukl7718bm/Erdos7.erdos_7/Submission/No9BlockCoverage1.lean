import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_16 : blockPrimeCoverageCheck 16=true := by decide +kernel
theorem block_prime_coverage_17 : blockPrimeCoverageCheck 17=true := by decide +kernel
theorem block_prime_coverage_18 : blockPrimeCoverageCheck 18=true := by decide +kernel
theorem block_prime_coverage_19 : blockPrimeCoverageCheck 19=true := by decide +kernel
theorem block_prime_coverage_20 : blockPrimeCoverageCheck 20=true := by decide +kernel
theorem block_prime_coverage_21 : blockPrimeCoverageCheck 21=true := by decide +kernel
theorem block_prime_coverage_22 : blockPrimeCoverageCheck 22=true := by decide +kernel
theorem block_prime_coverage_23 : blockPrimeCoverageCheck 23=true := by decide +kernel
theorem block_prime_coverage_24 : blockPrimeCoverageCheck 24=true := by decide +kernel
theorem block_prime_coverage_25 : blockPrimeCoverageCheck 25=true := by decide +kernel
theorem block_prime_coverage_26 : blockPrimeCoverageCheck 26=true := by decide +kernel
theorem block_prime_coverage_27 : blockPrimeCoverageCheck 27=true := by decide +kernel
theorem block_prime_coverage_28 : blockPrimeCoverageCheck 28=true := by decide +kernel
theorem block_prime_coverage_29 : blockPrimeCoverageCheck 29=true := by decide +kernel
theorem block_prime_coverage_30 : blockPrimeCoverageCheck 30=true := by decide +kernel
theorem block_prime_coverage_31 : blockPrimeCoverageCheck 31=true := by decide +kernel

theorem block_prime_coverages_1 (i : ℕ) (hi0 : 16 ≤ i) (hi1 : i < 32) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_16
  · exact block_prime_coverage_17
  · exact block_prime_coverage_18
  · exact block_prime_coverage_19
  · exact block_prime_coverage_20
  · exact block_prime_coverage_21
  · exact block_prime_coverage_22
  · exact block_prime_coverage_23
  · exact block_prime_coverage_24
  · exact block_prime_coverage_25
  · exact block_prime_coverage_26
  · exact block_prime_coverage_27
  · exact block_prime_coverage_28
  · exact block_prime_coverage_29
  · exact block_prime_coverage_30
  · exact block_prime_coverage_31

#print axioms block_prime_coverages_1
end Erdos7No9Certificate
