import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_176 : blockPrimeCoverageCheck 176=true := by decide +kernel
theorem block_prime_coverage_177 : blockPrimeCoverageCheck 177=true := by decide +kernel
theorem block_prime_coverage_178 : blockPrimeCoverageCheck 178=true := by decide +kernel
theorem block_prime_coverage_179 : blockPrimeCoverageCheck 179=true := by decide +kernel
theorem block_prime_coverage_180 : blockPrimeCoverageCheck 180=true := by decide +kernel
theorem block_prime_coverage_181 : blockPrimeCoverageCheck 181=true := by decide +kernel
theorem block_prime_coverage_182 : blockPrimeCoverageCheck 182=true := by decide +kernel
theorem block_prime_coverage_183 : blockPrimeCoverageCheck 183=true := by decide +kernel
theorem block_prime_coverage_184 : blockPrimeCoverageCheck 184=true := by decide +kernel
theorem block_prime_coverage_185 : blockPrimeCoverageCheck 185=true := by decide +kernel
theorem block_prime_coverage_186 : blockPrimeCoverageCheck 186=true := by decide +kernel
theorem block_prime_coverage_187 : blockPrimeCoverageCheck 187=true := by decide +kernel
theorem block_prime_coverage_188 : blockPrimeCoverageCheck 188=true := by decide +kernel
theorem block_prime_coverage_189 : blockPrimeCoverageCheck 189=true := by decide +kernel
theorem block_prime_coverage_190 : blockPrimeCoverageCheck 190=true := by decide +kernel
theorem block_prime_coverage_191 : blockPrimeCoverageCheck 191=true := by decide +kernel

theorem block_prime_coverages_11 (i : ℕ) (hi0 : 176 ≤ i) (hi1 : i < 192) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_176
  · exact block_prime_coverage_177
  · exact block_prime_coverage_178
  · exact block_prime_coverage_179
  · exact block_prime_coverage_180
  · exact block_prime_coverage_181
  · exact block_prime_coverage_182
  · exact block_prime_coverage_183
  · exact block_prime_coverage_184
  · exact block_prime_coverage_185
  · exact block_prime_coverage_186
  · exact block_prime_coverage_187
  · exact block_prime_coverage_188
  · exact block_prime_coverage_189
  · exact block_prime_coverage_190
  · exact block_prime_coverage_191

#print axioms block_prime_coverages_11
end Erdos7No9Certificate
