import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_179 : 3 ≤ primes 179 ∧ primes 179 ≤ 2503 ∧
    Row (primes 179) (states 179) (states 180) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
