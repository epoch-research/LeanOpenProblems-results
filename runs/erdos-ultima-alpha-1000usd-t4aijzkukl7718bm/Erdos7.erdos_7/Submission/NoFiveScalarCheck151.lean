import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_151 : 3 ≤ primes 151 ∧ primes 151 ≤ 2503 ∧
    Row (primes 151) (states 151) (states 152) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
