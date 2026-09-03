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
private def checkData14 : List ℤ :=
  DensePolynomialCertificate.add (mul f10 a4) (DensePolynomialCertificate.add (mul f9 a5) (DensePolynomialCertificate.add (mul f8 a6) (DensePolynomialCertificate.add (mul f7 a7) (DensePolynomialCertificate.add (mul f6 a8) (DensePolynomialCertificate.add (mul g9 b5) (DensePolynomialCertificate.add (mul g8 b6) (DensePolynomialCertificate.add (mul g7 b7) (DensePolynomialCertificate.add (mul g6 b8) (DensePolynomialCertificate.add (mul g5 b9) ([]))))))))))

private theorem checked14 : zero checkData14 = true := by
  decide +kernel


theorem check14 (w : ℚ) :
    evalList a4 w*evalList f10 w+
      evalList a5 w*evalList f9 w+
      evalList a6 w*evalList f8 w+
      evalList a7 w*evalList f7 w+
      evalList a8 w*evalList f6 w+
      evalList b5 w*evalList g9 w+
      evalList b6 w*evalList g8 w+
      evalList b7 w*evalList g7 w+
      evalList b8 w*evalList g6 w+
      evalList b9 w*evalList g5 w = 0 := by
  have he := eval_zero checkData14 w checked14
  have hn : evalList ([] : List ℤ) w = 0 := rfl
  simp only [checkData14, DensePolynomialCertificate.eval_add, DensePolynomialCertificate.eval_mul, eval_scale, hn, add_zero] at he
  change _ = _ at he
  simpa only [add_assoc, add_zero, mul_comm] using he


end
end Erdos322Research.QuinticWeightedResultantCertificate
