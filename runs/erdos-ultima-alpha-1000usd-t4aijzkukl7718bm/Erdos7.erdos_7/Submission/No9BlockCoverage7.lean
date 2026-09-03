import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_112 : blockPrimeCoverageCheck 112=true := by decide +kernel
theorem block_prime_coverage_113 : blockPrimeCoverageCheck 113=true := by decide +kernel
theorem block_prime_coverage_114 : blockPrimeCoverageCheck 114=true := by decide +kernel
theorem block_prime_coverage_115 : blockPrimeCoverageCheck 115=true := by decide +kernel
theorem block_prime_coverage_116 : blockPrimeCoverageCheck 116=true := by decide +kernel
theorem block_prime_coverage_117 : blockPrimeCoverageCheck 117=true := by decide +kernel
theorem block_prime_coverage_118 : blockPrimeCoverageCheck 118=true := by decide +kernel
theorem block_prime_coverage_119 : blockPrimeCoverageCheck 119=true := by decide +kernel
theorem block_prime_coverage_120 : blockPrimeCoverageCheck 120=true := by decide +kernel
theorem block_prime_coverage_121 : blockPrimeCoverageCheck 121=true := by decide +kernel
theorem block_prime_coverage_122 : blockPrimeCoverageCheck 122=true := by decide +kernel
theorem block_prime_coverage_123 : blockPrimeCoverageCheck 123=true := by decide +kernel
theorem block_prime_coverage_124 : blockPrimeCoverageCheck 124=true := by decide +kernel
theorem block_prime_coverage_125 : blockPrimeCoverageCheck 125=true := by decide +kernel
theorem block_prime_coverage_126 : blockPrimeCoverageCheck 126=true := by decide +kernel
theorem block_prime_coverage_127 : blockPrimeCoverageCheck 127=true := by decide +kernel

theorem block_prime_coverages_7 (i : ℕ) (hi0 : 112 ≤ i) (hi1 : i < 128) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_112
  · exact block_prime_coverage_113
  · exact block_prime_coverage_114
  · exact block_prime_coverage_115
  · exact block_prime_coverage_116
  · exact block_prime_coverage_117
  · exact block_prime_coverage_118
  · exact block_prime_coverage_119
  · exact block_prime_coverage_120
  · exact block_prime_coverage_121
  · exact block_prime_coverage_122
  · exact block_prime_coverage_123
  · exact block_prime_coverage_124
  · exact block_prime_coverage_125
  · exact block_prime_coverage_126
  · exact block_prime_coverage_127

#print axioms block_prime_coverages_7
end Erdos7No9Certificate
