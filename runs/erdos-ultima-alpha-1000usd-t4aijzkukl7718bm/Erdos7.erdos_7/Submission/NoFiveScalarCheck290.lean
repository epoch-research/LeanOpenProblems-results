import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_290 : 3 ≤ primes 290 ∧ primes 290 ≤ 2503 ∧
    Row (primes 290) (states 290) (states 291) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
