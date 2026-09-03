import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_48 : blockPrimeCoverageCheck 48=true := by decide +kernel
theorem block_prime_coverage_49 : blockPrimeCoverageCheck 49=true := by decide +kernel
theorem block_prime_coverage_50 : blockPrimeCoverageCheck 50=true := by decide +kernel
theorem block_prime_coverage_51 : blockPrimeCoverageCheck 51=true := by decide +kernel
theorem block_prime_coverage_52 : blockPrimeCoverageCheck 52=true := by decide +kernel
theorem block_prime_coverage_53 : blockPrimeCoverageCheck 53=true := by decide +kernel
theorem block_prime_coverage_54 : blockPrimeCoverageCheck 54=true := by decide +kernel
theorem block_prime_coverage_55 : blockPrimeCoverageCheck 55=true := by decide +kernel
theorem block_prime_coverage_56 : blockPrimeCoverageCheck 56=true := by decide +kernel
theorem block_prime_coverage_57 : blockPrimeCoverageCheck 57=true := by decide +kernel
theorem block_prime_coverage_58 : blockPrimeCoverageCheck 58=true := by decide +kernel
theorem block_prime_coverage_59 : blockPrimeCoverageCheck 59=true := by decide +kernel
theorem block_prime_coverage_60 : blockPrimeCoverageCheck 60=true := by decide +kernel
theorem block_prime_coverage_61 : blockPrimeCoverageCheck 61=true := by decide +kernel
theorem block_prime_coverage_62 : blockPrimeCoverageCheck 62=true := by decide +kernel
theorem block_prime_coverage_63 : blockPrimeCoverageCheck 63=true := by decide +kernel

theorem block_prime_coverages_3 (i : ℕ) (hi0 : 48 ≤ i) (hi1 : i < 64) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_48
  · exact block_prime_coverage_49
  · exact block_prime_coverage_50
  · exact block_prime_coverage_51
  · exact block_prime_coverage_52
  · exact block_prime_coverage_53
  · exact block_prime_coverage_54
  · exact block_prime_coverage_55
  · exact block_prime_coverage_56
  · exact block_prime_coverage_57
  · exact block_prime_coverage_58
  · exact block_prime_coverage_59
  · exact block_prime_coverage_60
  · exact block_prime_coverage_61
  · exact block_prime_coverage_62
  · exact block_prime_coverage_63

#print axioms block_prime_coverages_3
end Erdos7No9Certificate
