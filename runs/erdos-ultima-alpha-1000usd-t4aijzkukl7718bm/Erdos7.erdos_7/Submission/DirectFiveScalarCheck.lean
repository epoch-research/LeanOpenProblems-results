import Submission.DirectFiveScalarDefs

/-! Kernel replay of the exact direct-five root row. -/
namespace Erdos7DirectFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
set_option Elab.async false
lemma row_certificate_0 : Row (primes 0) (states 0) (states 1) := by
  unfold Row Erdos7NoFiveScalar.State.Good
  decide +kernel
#print axioms row_certificate_0
end Erdos7DirectFiveScalar
