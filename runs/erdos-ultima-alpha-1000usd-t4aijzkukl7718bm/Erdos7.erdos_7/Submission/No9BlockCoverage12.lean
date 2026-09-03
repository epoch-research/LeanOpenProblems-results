import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_192 : blockPrimeCoverageCheck 192=true := by decide +kernel
theorem block_prime_coverage_193 : blockPrimeCoverageCheck 193=true := by decide +kernel
theorem block_prime_coverage_194 : blockPrimeCoverageCheck 194=true := by decide +kernel
theorem block_prime_coverage_195 : blockPrimeCoverageCheck 195=true := by decide +kernel
theorem block_prime_coverage_196 : blockPrimeCoverageCheck 196=true := by decide +kernel
theorem block_prime_coverage_197 : blockPrimeCoverageCheck 197=true := by decide +kernel
theorem block_prime_coverage_198 : blockPrimeCoverageCheck 198=true := by decide +kernel
theorem block_prime_coverage_199 : blockPrimeCoverageCheck 199=true := by decide +kernel
theorem block_prime_coverage_200 : blockPrimeCoverageCheck 200=true := by decide +kernel
theorem block_prime_coverage_201 : blockPrimeCoverageCheck 201=true := by decide +kernel
theorem block_prime_coverage_202 : blockPrimeCoverageCheck 202=true := by decide +kernel
theorem block_prime_coverage_203 : blockPrimeCoverageCheck 203=true := by decide +kernel
theorem block_prime_coverage_204 : blockPrimeCoverageCheck 204=true := by decide +kernel
theorem block_prime_coverage_205 : blockPrimeCoverageCheck 205=true := by decide +kernel
theorem block_prime_coverage_206 : blockPrimeCoverageCheck 206=true := by decide +kernel
theorem block_prime_coverage_207 : blockPrimeCoverageCheck 207=true := by decide +kernel

theorem block_prime_coverages_12 (i : ℕ) (hi0 : 192 ≤ i) (hi1 : i < 208) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_192
  · exact block_prime_coverage_193
  · exact block_prime_coverage_194
  · exact block_prime_coverage_195
  · exact block_prime_coverage_196
  · exact block_prime_coverage_197
  · exact block_prime_coverage_198
  · exact block_prime_coverage_199
  · exact block_prime_coverage_200
  · exact block_prime_coverage_201
  · exact block_prime_coverage_202
  · exact block_prime_coverage_203
  · exact block_prime_coverage_204
  · exact block_prime_coverage_205
  · exact block_prime_coverage_206
  · exact block_prime_coverage_207

#print axioms block_prime_coverages_12
end Erdos7No9Certificate
