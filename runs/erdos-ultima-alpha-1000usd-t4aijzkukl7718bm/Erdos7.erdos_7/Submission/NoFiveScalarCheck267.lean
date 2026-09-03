import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_267 : 3 ≤ primes 267 ∧ primes 267 ≤ 2503 ∧
    Row (primes 267) (states 267) (states 268) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
