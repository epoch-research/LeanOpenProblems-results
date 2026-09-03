import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_144 : blockPrimeCoverageCheck 144=true := by decide +kernel
theorem block_prime_coverage_145 : blockPrimeCoverageCheck 145=true := by decide +kernel
theorem block_prime_coverage_146 : blockPrimeCoverageCheck 146=true := by decide +kernel
theorem block_prime_coverage_147 : blockPrimeCoverageCheck 147=true := by decide +kernel
theorem block_prime_coverage_148 : blockPrimeCoverageCheck 148=true := by decide +kernel
theorem block_prime_coverage_149 : blockPrimeCoverageCheck 149=true := by decide +kernel
theorem block_prime_coverage_150 : blockPrimeCoverageCheck 150=true := by decide +kernel
theorem block_prime_coverage_151 : blockPrimeCoverageCheck 151=true := by decide +kernel
theorem block_prime_coverage_152 : blockPrimeCoverageCheck 152=true := by decide +kernel
theorem block_prime_coverage_153 : blockPrimeCoverageCheck 153=true := by decide +kernel
theorem block_prime_coverage_154 : blockPrimeCoverageCheck 154=true := by decide +kernel
theorem block_prime_coverage_155 : blockPrimeCoverageCheck 155=true := by decide +kernel
theorem block_prime_coverage_156 : blockPrimeCoverageCheck 156=true := by decide +kernel
theorem block_prime_coverage_157 : blockPrimeCoverageCheck 157=true := by decide +kernel
theorem block_prime_coverage_158 : blockPrimeCoverageCheck 158=true := by decide +kernel
theorem block_prime_coverage_159 : blockPrimeCoverageCheck 159=true := by decide +kernel

theorem block_prime_coverages_9 (i : ℕ) (hi0 : 144 ≤ i) (hi1 : i < 160) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_144
  · exact block_prime_coverage_145
  · exact block_prime_coverage_146
  · exact block_prime_coverage_147
  · exact block_prime_coverage_148
  · exact block_prime_coverage_149
  · exact block_prime_coverage_150
  · exact block_prime_coverage_151
  · exact block_prime_coverage_152
  · exact block_prime_coverage_153
  · exact block_prime_coverage_154
  · exact block_prime_coverage_155
  · exact block_prime_coverage_156
  · exact block_prime_coverage_157
  · exact block_prime_coverage_158
  · exact block_prime_coverage_159

#print axioms block_prime_coverages_9
end Erdos7No9Certificate
