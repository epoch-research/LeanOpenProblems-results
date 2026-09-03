import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_37 : 3 ≤ primes 37 ∧ primes 37 ≤ 2503 ∧
    Row (primes 37) (states 37) (states 38) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
