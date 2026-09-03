import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_127 : 3 ≤ primes 127 ∧ primes 127 ≤ 2503 ∧
    Row (primes 127) (states 127) (states 128) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
