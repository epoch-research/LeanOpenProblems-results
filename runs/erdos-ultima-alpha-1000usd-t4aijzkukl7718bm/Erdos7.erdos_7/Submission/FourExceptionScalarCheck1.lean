import Submission.FourExceptionScalarDefs

/-! Kernel replay of the modified initial geometric row. -/
namespace Erdos7FourExceptionScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
set_option Elab.async false
lemma row_certificate_1 : Row (primes 1) (states 1) (states 2) := by
  unfold Row Erdos7NoFiveScalar.State.Good
  decide +kernel
#print axioms row_certificate_1
end Erdos7FourExceptionScalar
