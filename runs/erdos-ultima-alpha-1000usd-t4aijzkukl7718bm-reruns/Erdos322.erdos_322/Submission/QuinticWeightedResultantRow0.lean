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
private def checkData0 : List ℤ :=
  DensePolynomialCertificate.add (mul a0 f0) (DensePolynomialCertificate.add (mul b0 g0) (scale 274877906944 rootCoeffs))

private theorem checked0 : zero checkData0 = true := by
  decide +kernel


theorem check0 (w : ℚ) :
    evalList a0 w*evalList f0 w+
      evalList b0 w*evalList g0 w = (-274877906944)*target w := by
  have he := eval_zero checkData0 w checked0
  have hn : evalList ([] : List ℤ) w = 0 := rfl
  simp only [checkData0, DensePolynomialCertificate.eval_add, DensePolynomialCertificate.eval_mul, eval_scale, hn, add_zero] at he
  change _ = _ at he
  unfold target
  exact neg_scale_of_sum_eq_zero _ _ _ he


end
end Erdos322Research.QuinticWeightedResultantCertificate
