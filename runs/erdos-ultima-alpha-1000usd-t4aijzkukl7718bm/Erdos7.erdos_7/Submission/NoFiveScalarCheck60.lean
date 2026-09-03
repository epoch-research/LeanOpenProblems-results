import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_60 : 3 ≤ primes 60 ∧ primes 60 ≤ 2503 ∧
    Row (primes 60) (states 60) (states 61) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
