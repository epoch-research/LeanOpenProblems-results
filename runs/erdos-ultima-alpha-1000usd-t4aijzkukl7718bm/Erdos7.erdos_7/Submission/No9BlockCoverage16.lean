import Submission.No9SingleCoverage256
import Submission.No9SingleCoverage257
import Submission.No9SingleCoverage258
import Submission.No9SingleCoverage259
import Submission.No9SingleCoverage260
import Submission.No9SingleCoverage261
import Submission.No9SingleCoverage262
import Submission.No9SingleCoverage263
import Submission.No9SingleCoverage264
import Submission.No9SingleCoverage265
import Submission.No9SingleCoverage266
import Submission.No9SingleCoverage267
import Submission.No9SingleCoverage268
import Submission.No9SingleCoverage269
import Submission.No9SingleCoverage270
import Submission.No9SingleCoverage271

/-! Aggregate of independently checked intervals. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem block_prime_coverages_16 (i : ℕ) (hi0 : 256 ≤ i) (hi1 : i < 272) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_256
  · exact block_prime_coverage_257
  · exact block_prime_coverage_258
  · exact block_prime_coverage_259
  · exact block_prime_coverage_260
  · exact block_prime_coverage_261
  · exact block_prime_coverage_262
  · exact block_prime_coverage_263
  · exact block_prime_coverage_264
  · exact block_prime_coverage_265
  · exact block_prime_coverage_266
  · exact block_prime_coverage_267
  · exact block_prime_coverage_268
  · exact block_prime_coverage_269
  · exact block_prime_coverage_270
  · exact block_prime_coverage_271

#print axioms block_prime_coverages_16
end Erdos7No9Certificate
