import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_300 : 3 ≤ primes 300 ∧ primes 300 ≤ 2503 ∧
    Row (primes 300) (states 300) (states 301) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
