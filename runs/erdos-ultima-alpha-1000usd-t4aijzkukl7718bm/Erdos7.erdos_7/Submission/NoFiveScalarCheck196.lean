import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_196 : 3 ≤ primes 196 ∧ primes 196 ≤ 2503 ∧
    Row (primes 196) (states 196) (states 197) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
