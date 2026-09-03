import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_231 : 3 ≤ primes 231 ∧ primes 231 ≤ 2503 ∧
    Row (primes 231) (states 231) (states 232) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
