import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_104 : 3 ≤ primes 104 ∧ primes 104 ≤ 2503 ∧
    Row (primes 104) (states 104) (states 105) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
