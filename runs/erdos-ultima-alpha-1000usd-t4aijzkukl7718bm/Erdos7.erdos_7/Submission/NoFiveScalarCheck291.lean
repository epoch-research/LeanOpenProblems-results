import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_291 : 3 ≤ primes 291 ∧ primes 291 ≤ 2503 ∧
    Row (primes 291) (states 291) (states 292) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
