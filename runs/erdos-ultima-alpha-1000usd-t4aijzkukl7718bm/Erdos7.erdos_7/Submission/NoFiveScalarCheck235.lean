import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_235 : 3 ≤ primes 235 ∧ primes 235 ≤ 2503 ∧
    Row (primes 235) (states 235) (states 236) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
