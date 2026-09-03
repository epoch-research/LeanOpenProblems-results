import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_77 : 3 ≤ primes 77 ∧ primes 77 ≤ 2503 ∧
    Row (primes 77) (states 77) (states 78) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
