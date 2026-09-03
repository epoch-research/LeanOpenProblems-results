import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_266 : 3 ≤ primes 266 ∧ primes 266 ≤ 2503 ∧
    Row (primes 266) (states 266) (states 267) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
