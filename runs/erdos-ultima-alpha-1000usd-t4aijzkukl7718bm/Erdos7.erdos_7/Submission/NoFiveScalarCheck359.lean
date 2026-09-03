import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_359 : 3 ≤ primes 359 ∧ primes 359 ≤ 2503 ∧
    Row (primes 359) (states 359) (states 360) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
