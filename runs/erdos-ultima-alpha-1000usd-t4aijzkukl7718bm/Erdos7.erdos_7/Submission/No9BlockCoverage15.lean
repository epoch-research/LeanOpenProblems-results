import Submission.No9SingleCoverage240
import Submission.No9SingleCoverage241
import Submission.No9SingleCoverage242
import Submission.No9SingleCoverage243
import Submission.No9SingleCoverage244
import Submission.No9SingleCoverage245
import Submission.No9SingleCoverage246
import Submission.No9SingleCoverage247
import Submission.No9SingleCoverage248
import Submission.No9SingleCoverage249
import Submission.No9SingleCoverage250
import Submission.No9SingleCoverage251
import Submission.No9SingleCoverage252
import Submission.No9SingleCoverage253
import Submission.No9SingleCoverage254
import Submission.No9SingleCoverage255

/-! Aggregate of independently checked intervals. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem block_prime_coverages_15 (i : ℕ) (hi0 : 240 ≤ i) (hi1 : i < 256) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_240
  · exact block_prime_coverage_241
  · exact block_prime_coverage_242
  · exact block_prime_coverage_243
  · exact block_prime_coverage_244
  · exact block_prime_coverage_245
  · exact block_prime_coverage_246
  · exact block_prime_coverage_247
  · exact block_prime_coverage_248
  · exact block_prime_coverage_249
  · exact block_prime_coverage_250
  · exact block_prime_coverage_251
  · exact block_prime_coverage_252
  · exact block_prime_coverage_253
  · exact block_prime_coverage_254
  · exact block_prime_coverage_255

#print axioms block_prime_coverages_15
end Erdos7No9Certificate
