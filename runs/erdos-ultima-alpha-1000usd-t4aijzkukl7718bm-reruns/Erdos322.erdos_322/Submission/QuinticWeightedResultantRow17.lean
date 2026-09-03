import Submission.QuinticWeightedResultantData

/-! A coefficientwise certificate for a restricted quintic polynomial construction.
This module does not assert bounds for unrestricted representation counts. -/
namespace Erdos322Research.QuinticWeightedResultantCertificate
noncomputable section
open Polynomial Finset RationalPolynomialModularObstruction DensePolynomialCertificate
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
private def checkData17 : List ℤ :=
  DensePolynomialCertificate.add (mul f10 a7) (DensePolynomialCertificate.add (mul f9 a8) (DensePolynomialCertificate.add (mul g9 b8) (DensePolynomialCertificate.add (mul g8 b9) ([]))))

private theorem checked17 : zero checkData17 = true := by
  decide +kernel


theorem check17 (w : ℚ) :
    evalList a7 w*evalList f10 w+
      evalList a8 w*evalList f9 w+
      evalList b8 w*evalList g9 w+
      evalList b9 w*evalList g8 w = 0 := by
  have he := eval_zero checkData17 w checked17
  have hn : evalList ([] : List ℤ) w = 0 := rfl
  simp only [checkData17, DensePolynomialCertificate.eval_add, DensePolynomialCertificate.eval_mul, eval_scale, hn, add_zero] at he
  change _ = _ at he
  simpa only [add_assoc, add_zero, mul_comm] using he


end
end Erdos322Research.QuinticWeightedResultantCertificate
