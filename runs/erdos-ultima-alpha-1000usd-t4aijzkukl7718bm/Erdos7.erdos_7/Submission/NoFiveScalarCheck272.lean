import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_272 : 3 ≤ primes 272 ∧ primes 272 ≤ 2503 ∧
    Row (primes 272) (states 272) (states 273) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
