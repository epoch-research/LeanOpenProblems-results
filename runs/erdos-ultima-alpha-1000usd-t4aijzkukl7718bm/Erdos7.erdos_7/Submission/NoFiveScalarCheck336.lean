import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_336 : 3 ≤ primes 336 ∧ primes 336 ≤ 2503 ∧
    Row (primes 336) (states 336) (states 337) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
