import FormalConjecturesUtil

/-! The central quadratic construction cannot remove the basic degeneracy
of an equal-radius central source. This is a restricted obstruction, not
an answer to Erdős 213. -/
namespace Erdos213.CentralCircleDegeneration
open EuclideanGeometry
noncomputable section

lemma collinear_of_conjugate_cross (z w : ℂ)
    (h : starRingEnd ℂ z * w = z * starRingEnd ℂ w) :
    Collinear ℝ ({0,z,w} : Set ℂ) := by
  by_cases hw : w=0
  · subst w
    convert collinear_pair ℝ (0 : ℂ) z using 1
    ext a
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hbar : starRingEnd ℂ w ≠ 0 := by simpa using hw
  have he : starRingEnd ℂ (z/w)=z/w := by
    rw [map_div₀]
    exact (div_eq_div_iff hbar hw).mpr h
  have him := Complex.conj_eq_iff_im.mp he
  have hr : (((z/w).re : ℝ) : ℂ)=z/w := by
    apply Complex.ext <;> simp [him]
  apply (collinear_iff_of_mem (by simp : (0 : ℂ)∈({0,z,w} : Set ℂ))).mpr
  refine ⟨w,?_⟩
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with h0 | hz | hw
  · subst p
    exact ⟨0,by simp⟩
  · subst p
    refine ⟨(z/w).re,?_⟩
    rw [vadd_eq_add,Complex.real_smul,hr,div_mul_cancel₀ _ hw,add_zero]
  · subst p
    exact ⟨1,by simp⟩

/-- Equal source radii force two product points and the origin onto a line.
The source points need not have rational coordinates or rational distances. -/
theorem equal_radius_product_collinear (u v w : ℂ)
    (huv : ‖u‖=‖v‖) (huw : ‖u‖=‖w‖) :
    Collinear ℝ ({0,(u+v)*(u+w),(u-v)*(u-w)} : Set ℂ) := by
  have hUV : starRingEnd ℂ v*v-starRingEnd ℂ u*u=0 := by
    rw [← Complex.normSq_eq_conj_mul_self,← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,huv]
    simp
  have hUW : starRingEnd ℂ w*w-starRingEnd ℂ u*u=0 := by
    rw [← Complex.normSq_eq_conj_mul_self,← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,huw]
    simp
  apply collinear_of_conjugate_cross
  simp only [map_mul,map_add,map_sub]
  linear_combination
    (2*(starRingEnd ℂ u*w-starRingEnd ℂ w*u))*hUV +
    (2*(starRingEnd ℂ u*v-starRingEnd ℂ v*u))*hUW

/-- The second opposite pair of products has the same degeneracy. -/
theorem equal_radius_mixed_product_collinear (u v w : ℂ)
    (huv : ‖u‖=‖v‖) (huw : ‖u‖=‖w‖) :
    Collinear ℝ ({0,(u+v)*(u-w),(u-v)*(u+w)} : Set ℂ) := by
  simpa using equal_radius_product_collinear u v (-w) huv (by simpa using huw)

/-- For noncolliding source factors, this is a genuine failure of the
no-three-collinear condition on the full seven-point output. -/
theorem equal_radius_not_nontrilinear (u v w : ℂ)
    (huv : ‖u‖=‖v‖) (huw : ‖u‖=‖w‖)
    (hu : u≠0) (hpv : u+v≠0) (hmv : u-v≠0)
    (hpw : u+w≠0) (hmw : u-w≠0) (hvw : v+w≠0) :
    ¬NonTrilinear ({0,u^2-v^2,u^2-w^2,
      (u+v)*(u+w),(u+v)*(u-w),(u-v)*(u+w),(u-v)*(u-w)} : Set ℂ) := by
  have h0A : (0 : ℂ)≠(u+v)*(u+w) := (mul_ne_zero hpv hpw).symm
  have h0B : (0 : ℂ)≠(u-v)*(u-w) := (mul_ne_zero hmv hmw).symm
  have hAB : (u+v)*(u+w)≠(u-v)*(u-w) := by
    intro he
    apply mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ)≠0) hu) hvw
    calc
      2*u*(v+w) = (u+v)*(u+w)-(u-v)*(u-w) := by ring
      _ = 0 := sub_eq_zero.mpr he
  intro h
  exact h (by simp) (by simp) (by simp) h0A hAB h0B
    (equal_radius_product_collinear u v w huv huw)

#print axioms equal_radius_product_collinear
#print axioms equal_radius_mixed_product_collinear
#print axioms equal_radius_not_nontrilinear
end
end Erdos213.CentralCircleDegeneration
