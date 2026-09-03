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
private def checkData9 : List ℤ :=
  DensePolynomialCertificate.add (mul f9 a0) (DensePolynomialCertificate.add (mul f8 a1) (DensePolynomialCertificate.add (mul f7 a2) (DensePolynomialCertificate.add (mul f6 a3) (DensePolynomialCertificate.add (mul f5 a4) (DensePolynomialCertificate.add (mul f4 a5) (DensePolynomialCertificate.add (mul f3 a6) (DensePolynomialCertificate.add (mul f2 a7) (DensePolynomialCertificate.add (mul f1 a8) (DensePolynomialCertificate.add (mul g9 b0) (DensePolynomialCertificate.add (mul g8 b1) (DensePolynomialCertificate.add (mul g7 b2) (DensePolynomialCertificate.add (mul g6 b3) (DensePolynomialCertificate.add (mul g5 b4) (DensePolynomialCertificate.add (mul g4 b5) (DensePolynomialCertificate.add (mul g3 b6) (DensePolynomialCertificate.add (mul g2 b7) (DensePolynomialCertificate.add (mul g1 b8) (DensePolynomialCertificate.add (mul g0 b9) ([])))))))))))))))))))

private theorem checked9 : zero checkData9 = true := by
  decide +kernel


theorem check9 (w : ℚ) :
    evalList a0 w*evalList f9 w+
      evalList a1 w*evalList f8 w+
      evalList a2 w*evalList f7 w+
      evalList a3 w*evalList f6 w+
      evalList a4 w*evalList f5 w+
      evalList a5 w*evalList f4 w+
      evalList a6 w*evalList f3 w+
      evalList a7 w*evalList f2 w+
      evalList a8 w*evalList f1 w+
      evalList b0 w*evalList g9 w+
      evalList b1 w*evalList g8 w+
      evalList b2 w*evalList g7 w+
      evalList b3 w*evalList g6 w+
      evalList b4 w*evalList g5 w+
      evalList b5 w*evalList g4 w+
      evalList b6 w*evalList g3 w+
      evalList b7 w*evalList g2 w+
      evalList b8 w*evalList g1 w+
      evalList b9 w*evalList g0 w = 0 := by
  have he := eval_zero checkData9 w checked9
  have hn : evalList ([] : List ℤ) w = 0 := rfl
  simp only [checkData9, DensePolynomialCertificate.eval_add, DensePolynomialCertificate.eval_mul, eval_scale, hn, add_zero] at he
  change _ = _ at he
  simpa only [add_assoc, add_zero, mul_comm] using he


end
end Erdos322Research.QuinticWeightedResultantCertificate
