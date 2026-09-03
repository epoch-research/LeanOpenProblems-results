import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_296 : 3 ≤ primes 296 ∧ primes 296 ≤ 2503 ∧
    Row (primes 296) (states 296) (states 297) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
