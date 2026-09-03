import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_128 : blockPrimeCoverageCheck 128=true := by decide +kernel
theorem block_prime_coverage_129 : blockPrimeCoverageCheck 129=true := by decide +kernel
theorem block_prime_coverage_130 : blockPrimeCoverageCheck 130=true := by decide +kernel
theorem block_prime_coverage_131 : blockPrimeCoverageCheck 131=true := by decide +kernel
theorem block_prime_coverage_132 : blockPrimeCoverageCheck 132=true := by decide +kernel
theorem block_prime_coverage_133 : blockPrimeCoverageCheck 133=true := by decide +kernel
theorem block_prime_coverage_134 : blockPrimeCoverageCheck 134=true := by decide +kernel
theorem block_prime_coverage_135 : blockPrimeCoverageCheck 135=true := by decide +kernel
theorem block_prime_coverage_136 : blockPrimeCoverageCheck 136=true := by decide +kernel
theorem block_prime_coverage_137 : blockPrimeCoverageCheck 137=true := by decide +kernel
theorem block_prime_coverage_138 : blockPrimeCoverageCheck 138=true := by decide +kernel
theorem block_prime_coverage_139 : blockPrimeCoverageCheck 139=true := by decide +kernel
theorem block_prime_coverage_140 : blockPrimeCoverageCheck 140=true := by decide +kernel
theorem block_prime_coverage_141 : blockPrimeCoverageCheck 141=true := by decide +kernel
theorem block_prime_coverage_142 : blockPrimeCoverageCheck 142=true := by decide +kernel
theorem block_prime_coverage_143 : blockPrimeCoverageCheck 143=true := by decide +kernel

theorem block_prime_coverages_8 (i : ℕ) (hi0 : 128 ≤ i) (hi1 : i < 144) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_128
  · exact block_prime_coverage_129
  · exact block_prime_coverage_130
  · exact block_prime_coverage_131
  · exact block_prime_coverage_132
  · exact block_prime_coverage_133
  · exact block_prime_coverage_134
  · exact block_prime_coverage_135
  · exact block_prime_coverage_136
  · exact block_prime_coverage_137
  · exact block_prime_coverage_138
  · exact block_prime_coverage_139
  · exact block_prime_coverage_140
  · exact block_prime_coverage_141
  · exact block_prime_coverage_142
  · exact block_prime_coverage_143

#print axioms block_prime_coverages_8
end Erdos7No9Certificate
