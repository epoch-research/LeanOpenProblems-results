import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_280 : 3 ≤ primes 280 ∧ primes 280 ≤ 2503 ∧
    Row (primes 280) (states 280) (states 281) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
