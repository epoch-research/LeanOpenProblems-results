import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_228 : 3 ≤ primes 228 ∧ primes 228 ≤ 2503 ∧
    Row (primes 228) (states 228) (states 229) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
