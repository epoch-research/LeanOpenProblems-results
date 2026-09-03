import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_349 : 3 ≤ primes 349 ∧ primes 349 ≤ 2503 ∧
    Row (primes 349) (states 349) (states 350) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
