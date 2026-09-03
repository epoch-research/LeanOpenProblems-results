import Submission.No9SingleCoverage272
import Submission.No9SingleCoverage273
import Submission.No9SingleCoverage274
import Submission.No9SingleCoverage275
import Submission.No9SingleCoverage276
import Submission.No9SingleCoverage277
import Submission.No9SingleCoverage278
import Submission.No9SingleCoverage279
import Submission.No9SingleCoverage280
import Submission.No9SingleCoverage281
import Submission.No9SingleCoverage282
import Submission.No9SingleCoverage283
import Submission.No9SingleCoverage284
import Submission.No9SingleCoverage285
import Submission.No9SingleCoverage286
import Submission.No9SingleCoverage287

/-! Aggregate of independently checked intervals. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem block_prime_coverages_17 (i : ℕ) (hi0 : 272 ≤ i) (hi1 : i < 288) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_272
  · exact block_prime_coverage_273
  · exact block_prime_coverage_274
  · exact block_prime_coverage_275
  · exact block_prime_coverage_276
  · exact block_prime_coverage_277
  · exact block_prime_coverage_278
  · exact block_prime_coverage_279
  · exact block_prime_coverage_280
  · exact block_prime_coverage_281
  · exact block_prime_coverage_282
  · exact block_prime_coverage_283
  · exact block_prime_coverage_284
  · exact block_prime_coverage_285
  · exact block_prime_coverage_286
  · exact block_prime_coverage_287

#print axioms block_prime_coverages_17
end Erdos7No9Certificate
