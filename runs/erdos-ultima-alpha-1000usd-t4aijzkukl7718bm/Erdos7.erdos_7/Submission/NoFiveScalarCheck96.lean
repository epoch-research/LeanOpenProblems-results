import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_96 : 3 ≤ primes 96 ∧ primes 96 ≤ 2503 ∧
    Row (primes 96) (states 96) (states 97) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
