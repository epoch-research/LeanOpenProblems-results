import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_180 : 3 ≤ primes 180 ∧ primes 180 ≤ 2503 ∧
    Row (primes 180) (states 180) (states 181) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
