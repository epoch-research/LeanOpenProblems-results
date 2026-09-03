import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_144 : 3 ≤ primes 144 ∧ primes 144 ≤ 2503 ∧
    Row (primes 144) (states 144) (states 145) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
