import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_308 : 3 ≤ primes 308 ∧ primes 308 ≤ 2503 ∧
    Row (primes 308) (states 308) (states 309) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
