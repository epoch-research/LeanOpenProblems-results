import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_273 : 3 ≤ primes 273 ∧ primes 273 ≤ 2503 ∧
    Row (primes 273) (states 273) (states 274) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
