import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_136 : 3 ≤ primes 136 ∧ primes 136 ≤ 2503 ∧
    Row (primes 136) (states 136) (states 137) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
