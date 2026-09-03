import Submission.No9CoverageChecks

/-! Kernel-certified prime coverage via proper-factor witnesses. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000
theorem block_prime_coverage_160 : blockPrimeCoverageCheck 160=true := by decide +kernel
theorem block_prime_coverage_161 : blockPrimeCoverageCheck 161=true := by decide +kernel
theorem block_prime_coverage_162 : blockPrimeCoverageCheck 162=true := by decide +kernel
theorem block_prime_coverage_163 : blockPrimeCoverageCheck 163=true := by decide +kernel
theorem block_prime_coverage_164 : blockPrimeCoverageCheck 164=true := by decide +kernel
theorem block_prime_coverage_165 : blockPrimeCoverageCheck 165=true := by decide +kernel
theorem block_prime_coverage_166 : blockPrimeCoverageCheck 166=true := by decide +kernel
theorem block_prime_coverage_167 : blockPrimeCoverageCheck 167=true := by decide +kernel
theorem block_prime_coverage_168 : blockPrimeCoverageCheck 168=true := by decide +kernel
theorem block_prime_coverage_169 : blockPrimeCoverageCheck 169=true := by decide +kernel
theorem block_prime_coverage_170 : blockPrimeCoverageCheck 170=true := by decide +kernel
theorem block_prime_coverage_171 : blockPrimeCoverageCheck 171=true := by decide +kernel
theorem block_prime_coverage_172 : blockPrimeCoverageCheck 172=true := by decide +kernel
theorem block_prime_coverage_173 : blockPrimeCoverageCheck 173=true := by decide +kernel
theorem block_prime_coverage_174 : blockPrimeCoverageCheck 174=true := by decide +kernel
theorem block_prime_coverage_175 : blockPrimeCoverageCheck 175=true := by decide +kernel

theorem block_prime_coverages_10 (i : ℕ) (hi0 : 160 ≤ i) (hi1 : i < 176) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_160
  · exact block_prime_coverage_161
  · exact block_prime_coverage_162
  · exact block_prime_coverage_163
  · exact block_prime_coverage_164
  · exact block_prime_coverage_165
  · exact block_prime_coverage_166
  · exact block_prime_coverage_167
  · exact block_prime_coverage_168
  · exact block_prime_coverage_169
  · exact block_prime_coverage_170
  · exact block_prime_coverage_171
  · exact block_prime_coverage_172
  · exact block_prime_coverage_173
  · exact block_prime_coverage_174
  · exact block_prime_coverage_175

#print axioms block_prime_coverages_10
end Erdos7No9Certificate
