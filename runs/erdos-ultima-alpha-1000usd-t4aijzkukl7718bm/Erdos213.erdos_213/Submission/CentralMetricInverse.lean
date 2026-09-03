import Submission.CentralReflection

/-! Exact metric inverse for the normalized central-heptad construction.
This is a construction-specific result, not an unrestricted cardinality bound. -/
namespace Erdos213.CentralMetricInverse
open CentralQuadratic CentralReflection
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000

def scaledDiff (L t w : ℂ) (i j : Fin 7) : ℂ :=
  L*(points t w i-points t w j)

lemma diff_ne_zero (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w)) (i j : Fin 7) (hij : i≠j) :
    scaledDiff L t w i j≠0 :=
  mul_ne_zero hL (sub_ne_zero.mpr (fun h => hij (hi h)))

lemma recover_t (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w)) :
    scaledDiff L t w 3 5*scaledDiff L t w 2 1/(scaledDiff L t w 3 2*scaledDiff L t w 4 5)=t := by
  apply (div_eq_iff (mul_ne_zero (diff_ne_zero L t w hL hi 3 2 (by decide)) (diff_ne_zero L t w hL hi 4 5 (by decide)))).mpr
  change (L*(((1+t)*(1+w))-((1-t)*(1+w))))*(L*((1-w^2)-(1-t^2)))=(t)*((L*(((1+t)*(1+w))-(1-w^2)))*(L*(((1+t)*(1-w))-((1-t)*(1+w)))))
  ring


lemma recover_w (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w)) :
    scaledDiff L t w 3 4*scaledDiff L t w 2 1/(scaledDiff L t w 3 1*scaledDiff L t w 4 5)=w := by
  apply (div_eq_iff (mul_ne_zero (diff_ne_zero L t w hL hi 3 1 (by decide)) (diff_ne_zero L t w hL hi 4 5 (by decide)))).mpr
  change (L*(((1+t)*(1+w))-((1+t)*(1-w))))*(L*((1-w^2)-(1-t^2)))=(w)*((L*(((1+t)*(1+w))-(1-t^2)))*(L*(((1+t)*(1-w))-((1-t)*(1+w)))))
  ring


lemma recover_one_add_t (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w)) :
    2*scaledDiff L t w 3 1/(scaledDiff L t w 3 6)=1+t := by
  apply (div_eq_iff ((diff_ne_zero L t w hL hi 3 6 (by decide)))).mpr
  change 2*(L*(((1+t)*(1+w))-(1-t^2)))=(1+t)*((L*(((1+t)*(1+w))-((1-t)*(1-w)))))
  ring


lemma recover_one_sub_t (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w)) :
    2*scaledDiff L t w 1 6/(scaledDiff L t w 3 6)=1-t := by
  apply (div_eq_iff ((diff_ne_zero L t w hL hi 3 6 (by decide)))).mpr
  change 2*(L*((1-t^2)-((1-t)*(1-w))))=(1-t)*((L*(((1+t)*(1+w))-((1-t)*(1-w)))))
  ring


lemma recover_one_add_w (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w)) :
    2*scaledDiff L t w 3 2/(scaledDiff L t w 3 6)=1+w := by
  apply (div_eq_iff ((diff_ne_zero L t w hL hi 3 6 (by decide)))).mpr
  change 2*(L*(((1+t)*(1+w))-(1-w^2)))=(1+w)*((L*(((1+t)*(1+w))-((1-t)*(1-w)))))
  ring


lemma recover_one_sub_w (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w)) :
    2*scaledDiff L t w 2 6/(scaledDiff L t w 3 6)=1-w := by
  apply (div_eq_iff ((diff_ne_zero L t w hL hi 3 6 (by decide)))).mpr
  change 2*(L*((1-w^2)-((1-t)*(1-w))))=(1-w)*((L*(((1+t)*(1+w))-((1-t)*(1-w)))))
  ring


lemma recover_t_add_w (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w)) :
    2*scaledDiff L t w 2 1/(scaledDiff L t w 4 5)=t+w := by
  apply (div_eq_iff ((diff_ne_zero L t w hL hi 4 5 (by decide)))).mpr
  change 2*(L*((1-w^2)-(1-t^2)))=(t+w)*((L*(((1+t)*(1-w))-((1-t)*(1+w)))))
  ring


lemma recover_t_sub_w (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w)) :
    2*scaledDiff L t w 2 1/(scaledDiff L t w 3 6)=t-w := by
  apply (div_eq_iff ((diff_ne_zero L t w hL hi 3 6 (by decide)))).mpr
  change 2*(L*((1-w^2)-(1-t^2)))=(t-w)*((L*(((1+t)*(1+w))-((1-t)*(1-w)))))
  ring


lemma norm_div {z w : ℂ} (hz : RationalNorm z) (hw : RationalNorm w) :
    RationalNorm (z/w) := by
  obtain ⟨a,ha⟩ := hz
  obtain ⟨b,hb⟩ := hw
  exact ⟨a/b,by simp only [Rat.cast_div,ha,hb,_root_.norm_div]⟩

/-- Rational output distances, even after an arbitrary nonzero complex scale,
force all normalized source norms to be rational. -/
theorem factors_of_scaled_output_distances (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w))
    (hd : ∀ i j, dist (L*points t w i) (L*points t w j)∈
      Set.range ((↑) : ℚ → ℝ)) :
    ∀ k, RationalNorm (factors 1 t w k) := by
  have hD (i j : Fin 7) : RationalNorm (scaledDiff L t w i j) := by
    simpa only [dist_eq_norm,← mul_sub] using hd i j
  have h2 : RationalNorm (2 : ℂ) := ⟨2,by norm_num⟩
  intro k
  fin_cases k
  · exact ⟨1,by norm_num [factors]⟩
  · change RationalNorm (t)
    rw [← recover_t L t w hL hi]
    exact norm_div ((hD 3 5).mul (hD 2 1)) ((hD 3 2).mul (hD 4 5))
  · change RationalNorm (w)
    rw [← recover_w L t w hL hi]
    exact norm_div ((hD 3 4).mul (hD 2 1)) ((hD 3 1).mul (hD 4 5))
  · change RationalNorm (1+t)
    rw [← recover_one_add_t L t w hL hi]
    exact norm_div (h2.mul (hD 3 1)) (hD 3 6)
  · change RationalNorm (1-t)
    rw [← recover_one_sub_t L t w hL hi]
    exact norm_div (h2.mul (hD 1 6)) (hD 3 6)
  · change RationalNorm (1+w)
    rw [← recover_one_add_w L t w hL hi]
    exact norm_div (h2.mul (hD 3 2)) (hD 3 6)
  · change RationalNorm (1-w)
    rw [← recover_one_sub_w L t w hL hi]
    exact norm_div (h2.mul (hD 2 6)) (hD 3 6)
  · change RationalNorm (t+w)
    rw [← recover_t_add_w L t w hL hi]
    exact norm_div (h2.mul (hD 2 1)) (hD 4 5)
  · change RationalNorm (t-w)
    rw [← recover_t_sub_w L t w hL hi]
    exact norm_div (h2.mul (hD 2 1)) (hD 3 6)

/-- The scale itself must also have rational norm. -/
theorem scale_of_output_distances (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w))
    (hd : ∀ i j, dist (L*points t w i) (L*points t w j)∈
      Set.range ((↑) : ℚ → ℝ)) : RationalNorm L := by
  have hf := factors_of_scaled_output_distances L t w hL hi hd
  have htw : t+w≠0 := by
    intro hh
    have he : points t w 3=points t w 6 := by
      change (1+t)*(1+w)=(1-t)*(1-w)
      linear_combination 2*hh
    exact (show (3 : Fin 7)≠6 by decide) (hi he)
  have hD : RationalNorm (scaledDiff L t w 3 6) := by
    simpa only [dist_eq_norm,← mul_sub] using hd 3 6
  have he : scaledDiff L t w 3 6/(2*(t+w))=L := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) htw)).mpr
    change L*((1+t)*(1+w)-(1-t)*(1-w))=L*(2*(t+w))
    ring
  rw [← he]
  have h2 : RationalNorm (2 : ℂ) := ⟨2,by norm_num⟩
  exact norm_div hD (h2.mul (hf 7))

lemma point_one_eq (t w : ℂ) (i : Fin 7) :
    CentralQuadratic.point 1 t w i=points t w i := by
  fin_cases i <;> simp [CentralQuadratic.point,points]

/-- A complete metric characterization of distinct normalized outputs. -/
theorem scaled_output_distances_iff (L t w : ℂ) (hL : L≠0)
    (hi : Function.Injective (points t w)) :
    (∀ i j, dist (L*points t w i) (L*points t w j)∈
      Set.range ((↑) : ℚ → ℝ)) ↔
    RationalNorm L ∧ ∀ k, RationalNorm (factors 1 t w k) := by
  constructor
  · intro hd
    exact ⟨scale_of_output_distances L t w hL hi hd,
      factors_of_scaled_output_distances L t w hL hi hd⟩
  · rintro ⟨hLn,hf⟩ i j
    have hd0 := CentralQuadratic.point_rational_distances 1 t w hf i j
    change RationalNorm (CentralQuadratic.point 1 t w i-CentralQuadratic.point 1 t w j) at hd0
    rw [point_one_eq,point_one_eq] at hd0
    have hh := hLn.mul hd0
    simpa only [RationalNorm,dist_eq_norm,← mul_sub] using hh

#print axioms scaled_output_distances_iff

#print axioms recover_t
#print axioms recover_w
#print axioms factors_of_scaled_output_distances
#print axioms scale_of_output_distances
end
end Erdos213.CentralMetricInverse
