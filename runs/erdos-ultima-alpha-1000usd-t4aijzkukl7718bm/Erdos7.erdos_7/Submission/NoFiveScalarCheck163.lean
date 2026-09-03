import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_163 : 3 ≤ primes 163 ∧ primes 163 ≤ 2503 ∧
    Row (primes 163) (states 163) (states 164) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
