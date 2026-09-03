import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_289 : 3 ≤ primes 289 ∧ primes 289 ≤ 2503 ∧
    Row (primes 289) (states 289) (states 290) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
