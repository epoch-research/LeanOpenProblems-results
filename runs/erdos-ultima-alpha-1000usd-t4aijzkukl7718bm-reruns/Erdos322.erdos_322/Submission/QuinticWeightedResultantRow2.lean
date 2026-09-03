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
private def checkData2 : List ℤ :=
  DensePolynomialCertificate.add (mul a0 f2) (DensePolynomialCertificate.add (mul a1 f1) (DensePolynomialCertificate.add (mul a2 f0) (DensePolynomialCertificate.add (mul b0 g2) (DensePolynomialCertificate.add (mul b1 g1) (DensePolynomialCertificate.add (mul b2 g0) ([]))))))

private theorem checked2 : zero checkData2 = true := by
  decide +kernel


theorem check2 (w : ℚ) :
    evalList a0 w*evalList f2 w+
      evalList a1 w*evalList f1 w+
      evalList a2 w*evalList f0 w+
      evalList b0 w*evalList g2 w+
      evalList b1 w*evalList g1 w+
      evalList b2 w*evalList g0 w = 0 := by
  have he := eval_zero checkData2 w checked2
  have hn : evalList ([] : List ℤ) w = 0 := rfl
  simp only [checkData2, DensePolynomialCertificate.eval_add, DensePolynomialCertificate.eval_mul, eval_scale, hn, add_zero] at he
  change _ = _ at he
  simpa only [add_assoc, add_zero] using he


end
end Erdos322Research.QuinticWeightedResultantCertificate
