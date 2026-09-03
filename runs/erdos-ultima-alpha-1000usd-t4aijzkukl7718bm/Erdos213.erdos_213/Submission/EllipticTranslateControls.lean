import Submission.EllipticTranslateCircle

/-! Exact nonexceptional controls for elliptic translation. A rational-distance
triangle is present, but doubling the rational source does not preserve the
required distances. No claim about the unrestricted Erdős conjecture is made. -/
namespace Erdos213.EllipticTranslateControls
open EllipticTranslate
noncomputable section

private def A : ℚ := 9/4
private def B : ℚ := -9/4

lemma source_control :
    (1 : ℚ)^2=value A B 1 ∧
    (-5741/512 : ℚ)^2=value A B (313/64) ∧
    doubleX A B 1=313/64 ∧
    -1+((3+ A)/2)*(1-(313/64 : ℚ))= -5741/512 ∧
    doubleX A B 0= -9/16 ∧ value A B 0 < 0 := by
  norm_num [A,B,value,doubleX]

lemma positive_point : point A B 0 1 1 = (-3/2 : ℂ)-2*Complex.I := by
  have hroot : Real.sqrt (9/4 : ℝ)=3/2 := by norm_num [Real.sqrt_div]
  apply Complex.ext <;> norm_num [point,EllipticTranslate.realPart,imagCoeff,numerator,value,A,B,hroot]

lemma negative_point : point A B 0 1 (-1) = (-3/2 : ℂ)+2*Complex.I := by
  have hroot : Real.sqrt (9/4 : ℝ)=3/2 := by norm_num [Real.sqrt_div]
  apply Complex.ext <;> norm_num [point,EllipticTranslate.realPart,imagCoeff,numerator,value,A,B,hroot]

lemma identity_point : center A B 0 0=0 := by
  apply Complex.ext <;> simp [center]

lemma doubled_point : point A B 0 (313/64) (-5741/512) =
    (17760/97969 : ℂ)+(91856/97969 : ℂ)*Complex.I := by
  have hroot : Real.sqrt (9/4 : ℝ)=3/2 := by norm_num [Real.sqrt_div]
  apply Complex.ext <;> norm_num [point,EllipticTranslate.realPart,imagCoeff,numerator,value,A,B,hroot]

lemma triangle_lengths :
    dist (point A B 0 1 1) (center A B 0 0)=5/2 ∧
    dist (point A B 0 1 (-1)) (center A B 0 0)=5/2 ∧
    dist (point A B 0 1 1) (point A B 0 1 (-1))=4 := by
  rw [positive_point,negative_point,identity_point]
  norm_num [dist_eq_norm,Complex.norm_def,Complex.normSq_apply,Real.sqrt_div]

lemma triangle_area :
    (point A B 0 1 1).re*(point A B 0 1 (-1)).im-
      (point A B 0 1 1).im*(point A B 0 1 (-1)).re = -6 := by
  rw [positive_point,negative_point]
  norm_num

lemma doubling_fails :
    dist (point A B 0 (313/64) (-5741/512)) (center A B 0 0) ∉
      Set.range ((↑) : ℚ → ℝ) := by
  rw [origin_distance_iff A B 0 (313/64) (-5741/512)
    (by norm_num [A,B,value]) (by norm_num) (by norm_num [A,B,value])]
  norm_num [doubleX,A,B,value]

lemma not_symbolic_square :
    ¬ IsSquare (algebraMap EllipticDuplication.F (EllipticDuplication.E A B)
      (EllipticDuplication.lift (EllipticDuplication.quartic A B (doubleX A B 0))/
        (4*EllipticDuplication.lift (EllipticDuplication.cubic A B)))) := by
  rw [EllipticDuplication.elliptic_square_iff]
  norm_num [A,B,doubleX,value]

#print axioms source_control
#print axioms triangle_lengths
#print axioms triangle_area
#print axioms doubling_fails
#print axioms not_symbolic_square
end
end Erdos213.EllipticTranslateControls
