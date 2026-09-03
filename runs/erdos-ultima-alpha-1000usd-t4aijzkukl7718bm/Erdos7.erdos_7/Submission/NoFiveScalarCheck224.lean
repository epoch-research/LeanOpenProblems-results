import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_224 : 3 ≤ primes 224 ∧ primes 224 ≤ 2503 ∧
    Row (primes 224) (states 224) (states 225) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
