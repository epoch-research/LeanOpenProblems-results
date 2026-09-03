import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_97 : 3 ≤ primes 97 ∧ primes 97 ≤ 2503 ∧
    Row (primes 97) (states 97) (states 98) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
