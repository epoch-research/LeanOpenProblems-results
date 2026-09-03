import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_177 : 3 ≤ primes 177 ∧ primes 177 ≤ 2503 ∧
    Row (primes 177) (states 177) (states 178) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
