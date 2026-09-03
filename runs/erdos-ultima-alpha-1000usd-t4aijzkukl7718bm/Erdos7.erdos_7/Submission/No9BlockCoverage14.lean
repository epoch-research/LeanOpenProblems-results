import Submission.No9SingleCoverage224
import Submission.No9SingleCoverage225
import Submission.No9SingleCoverage226
import Submission.No9SingleCoverage227
import Submission.No9SingleCoverage228
import Submission.No9SingleCoverage229
import Submission.No9SingleCoverage230
import Submission.No9SingleCoverage231
import Submission.No9SingleCoverage232
import Submission.No9SingleCoverage233
import Submission.No9SingleCoverage234
import Submission.No9SingleCoverage235
import Submission.No9SingleCoverage236
import Submission.No9SingleCoverage237
import Submission.No9SingleCoverage238
import Submission.No9SingleCoverage239

/-! Aggregate of independently checked intervals. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem block_prime_coverages_14 (i : ℕ) (hi0 : 224 ≤ i) (hi1 : i < 240) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_224
  · exact block_prime_coverage_225
  · exact block_prime_coverage_226
  · exact block_prime_coverage_227
  · exact block_prime_coverage_228
  · exact block_prime_coverage_229
  · exact block_prime_coverage_230
  · exact block_prime_coverage_231
  · exact block_prime_coverage_232
  · exact block_prime_coverage_233
  · exact block_prime_coverage_234
  · exact block_prime_coverage_235
  · exact block_prime_coverage_236
  · exact block_prime_coverage_237
  · exact block_prime_coverage_238
  · exact block_prime_coverage_239

#print axioms block_prime_coverages_14
end Erdos7No9Certificate
