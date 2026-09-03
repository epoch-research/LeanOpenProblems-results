import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_259 : 3 ≤ primes 259 ∧ primes 259 ≤ 2503 ∧
    Row (primes 259) (states 259) (states 260) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
