import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_201 : 3 ≤ primes 201 ∧ primes 201 ≤ 2503 ∧
    Row (primes 201) (states 201) (states 202) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
