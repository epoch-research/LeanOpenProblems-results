import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_288 : 3 ≤ primes 288 ∧ primes 288 ≤ 2503 ∧
    Row (primes 288) (states 288) (states 289) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
