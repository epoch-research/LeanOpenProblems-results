import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_96 : blockPrimeCoverageCheck 96=true := by decide +kernel
theorem block_prime_coverage_97 : blockPrimeCoverageCheck 97=true := by decide +kernel
theorem block_prime_coverage_98 : blockPrimeCoverageCheck 98=true := by decide +kernel
theorem block_prime_coverage_99 : blockPrimeCoverageCheck 99=true := by decide +kernel
theorem block_prime_coverage_100 : blockPrimeCoverageCheck 100=true := by decide +kernel
theorem block_prime_coverage_101 : blockPrimeCoverageCheck 101=true := by decide +kernel
theorem block_prime_coverage_102 : blockPrimeCoverageCheck 102=true := by decide +kernel
theorem block_prime_coverage_103 : blockPrimeCoverageCheck 103=true := by decide +kernel
theorem block_prime_coverage_104 : blockPrimeCoverageCheck 104=true := by decide +kernel
theorem block_prime_coverage_105 : blockPrimeCoverageCheck 105=true := by decide +kernel
theorem block_prime_coverage_106 : blockPrimeCoverageCheck 106=true := by decide +kernel
theorem block_prime_coverage_107 : blockPrimeCoverageCheck 107=true := by decide +kernel
theorem block_prime_coverage_108 : blockPrimeCoverageCheck 108=true := by decide +kernel
theorem block_prime_coverage_109 : blockPrimeCoverageCheck 109=true := by decide +kernel
theorem block_prime_coverage_110 : blockPrimeCoverageCheck 110=true := by decide +kernel
theorem block_prime_coverage_111 : blockPrimeCoverageCheck 111=true := by decide +kernel

theorem block_prime_coverages_6 (i : ℕ) (hi0 : 96 ≤ i) (hi1 : i < 112) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_96
  · exact block_prime_coverage_97
  · exact block_prime_coverage_98
  · exact block_prime_coverage_99
  · exact block_prime_coverage_100
  · exact block_prime_coverage_101
  · exact block_prime_coverage_102
  · exact block_prime_coverage_103
  · exact block_prime_coverage_104
  · exact block_prime_coverage_105
  · exact block_prime_coverage_106
  · exact block_prime_coverage_107
  · exact block_prime_coverage_108
  · exact block_prime_coverage_109
  · exact block_prime_coverage_110
  · exact block_prime_coverage_111

#print axioms block_prime_coverages_6
end Erdos7No9Certificate
