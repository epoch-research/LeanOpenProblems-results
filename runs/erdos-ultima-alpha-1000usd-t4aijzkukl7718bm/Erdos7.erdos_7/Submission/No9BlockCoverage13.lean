import Submission.No9SingleCoverage208
import Submission.No9SingleCoverage209
import Submission.No9SingleCoverage210
import Submission.No9SingleCoverage211
import Submission.No9SingleCoverage212
import Submission.No9SingleCoverage213
import Submission.No9SingleCoverage214
import Submission.No9SingleCoverage215
import Submission.No9SingleCoverage216
import Submission.No9SingleCoverage217
import Submission.No9SingleCoverage218
import Submission.No9SingleCoverage219
import Submission.No9SingleCoverage220
import Submission.No9SingleCoverage221
import Submission.No9SingleCoverage222
import Submission.No9SingleCoverage223

/-! Aggregate of independently checked intervals. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem block_prime_coverages_13 (i : ℕ) (hi0 : 208 ≤ i) (hi1 : i < 224) : blockPrimeCoverageCheck i=true := by
  interval_cases i
  · exact block_prime_coverage_208
  · exact block_prime_coverage_209
  · exact block_prime_coverage_210
  · exact block_prime_coverage_211
  · exact block_prime_coverage_212
  · exact block_prime_coverage_213
  · exact block_prime_coverage_214
  · exact block_prime_coverage_215
  · exact block_prime_coverage_216
  · exact block_prime_coverage_217
  · exact block_prime_coverage_218
  · exact block_prime_coverage_219
  · exact block_prime_coverage_220
  · exact block_prime_coverage_221
  · exact block_prime_coverage_222
  · exact block_prime_coverage_223

#print axioms block_prime_coverages_13
end Erdos7No9Certificate
