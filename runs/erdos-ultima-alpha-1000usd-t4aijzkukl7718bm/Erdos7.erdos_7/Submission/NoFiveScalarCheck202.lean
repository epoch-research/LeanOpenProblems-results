import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_202 : 3 ≤ primes 202 ∧ primes 202 ≤ 2503 ∧
    Row (primes 202) (states 202) (states 203) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
