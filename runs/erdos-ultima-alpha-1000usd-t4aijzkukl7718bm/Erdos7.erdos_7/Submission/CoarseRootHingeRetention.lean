import Submission.CoarseRootRetention

/-! A sharper conditional common-coarse-root bound, using the first tail
hinges in addition to the tail means. This is not a disproof of Erdos7. -/
namespace Erdos7CoarseRootHingeRetention
open scoped BigOperators
open Erdos7CoarseRootRetention
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma clipped_product_minorant (A B u v : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    A*B-B*u-A*v+min 1 u*min 1 v ≤ max 0 (A-u)*max 0 (B-v) := by
  have hmu : 0 ≤ min 1 u := le_min (by norm_num) hu
  have hmv : 0 ≤ min 1 v := le_min (by norm_num) hv
  by_cases hau : u ≤ A
  · rw [max_eq_right (sub_nonneg.mpr hau)]
    by_cases hbv : v ≤ B
    · rw [max_eq_right (sub_nonneg.mpr hbv)]
      have hp := mul_le_mul (min_le_right 1 u) (min_le_right 1 v) hmv hu
      nlinarith
    · rw [max_eq_left (by linarith : B-v ≤ 0), mul_zero]
      have hp := mul_le_mul (min_le_right 1 u) ((min_le_left 1 v).trans hB) hmv hu
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ A) (by linarith : B-v ≤ 0)]
  · rw [max_eq_left (by linarith : A-u ≤ 0), zero_mul]
    have hp := mul_le_mul ((min_le_left 1 u).trans hA) (min_le_right 1 v) hmv (by linarith : 0 ≤ A)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : A-u ≤ 0) (by linarith : 0 ≤ B)]

lemma retention_product_minorant (a b u v d : ℝ)
    (ha : a ∈ Set.Icc (1:ℝ) 2) (hb : b ∈ Set.Icc (1:ℝ) 2)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (24-6*a-4*b+a*b-(6-b)*u-(4-a)*v+min 1 u*min 1 v-d)/24 ≤
      retention (a+u) (b+v) d := by
  have hh := clipped_product_minorant (4-a) (6-b) u v
    (by linarith [ha.2]) (by linarith [hb.2]) hu hv
  have h₁ : max 0 (4-a-u) = 4*max 0 (1-(a+u)/4) := by
    by_cases h : a+u ≤ 4
    · rw [max_eq_right (by linarith : 0 ≤ 4-a-u), max_eq_right (by linarith : 0 ≤ 1-(a+u)/4)]
      ring
    · rw [max_eq_left (by linarith : 4-a-u ≤ 0), max_eq_left (by linarith : 1-(a+u)/4 ≤ 0)]
      ring
  have h₂ : max 0 (6-b-v) = 6*max 0 (1-(b+v)/6) := by
    by_cases h : b+v ≤ 6
    · rw [max_eq_right (by linarith : 0 ≤ 6-b-v), max_eq_right (by linarith : 0 ≤ 1-(b+v)/6)]
      ring
    · rw [max_eq_left (by linarith : 6-b-v ≤ 0), max_eq_left (by linarith : 1-(b+v)/6 ≤ 0)]
      ring
  rw [h₁,h₂] at hh
  have hr : max 0 (1-(a+u)/4)*max 0 (1-(b+v)/6)-d/24 ≤ retention (a+u) (b+v) d := le_max_right _ _
  nlinarith

lemma tail_pair_hinge (u v : ℝ) :
    u+v-min 1 u*min 1 v ≤ 1+max 0 (u-1)+max 0 (v-1) := by
  have h₁ : u = min 1 u+max 0 (u-1) := by
    by_cases h : u ≤ 1
    · rw [min_eq_right h, max_eq_left (by linarith : u-1 ≤ 0)]; ring
    · rw [min_eq_left (by linarith : 1 ≤ u), max_eq_right (by linarith : 0 ≤ u-1)]; ring
  have h₂ : v = min 1 v+max 0 (v-1) := by
    by_cases h : v ≤ 1
    · rw [min_eq_right h, max_eq_left (by linarith : v-1 ≤ 0)]; ring
    · rw [min_eq_left (by linarith : 1 ≤ v), max_eq_right (by linarith : 0 ≤ v-1)]; ring
  have hh := mul_nonneg (sub_nonneg.mpr (min_le_left 1 u)) (sub_nonneg.mpr (min_le_left 1 v))
  nlinarith

/-- The mixed tail cost can be paid by one unit on the smaller branch and
two tail hinges. The two removal families remain distinct. -/
lemma branch_hinge_minorant (y z u v d : ℝ) (q : Bool)
    (hy : y ∈ Set.Icc (0:ℝ) 1) (hz : z ∈ Set.Icc (0:ℝ) 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (24-6*base y q-4*base z q+base y q*base z q-
      (5-z)*u-(3-y)*v-d-(if q then 0 else 1)-max 0 (u-1)-max 0 (v-1))/24 ≤
      retention (base y q+u) (base z q+v) d := by
  have hh := retention_product_minorant (base y q) (base z q) u v d
    (base_bounds y hy q) (base_bounds z hz q) hu hv
  have hmuv := mul_nonneg (le_min (by norm_num : (0:ℝ) ≤ 1) hu)
    (le_min (by norm_num : (0:ℝ) ≤ 1) hv)
  have hh₁ := le_max_left 0 (u-1)
  have hh₂ := le_max_left 0 (v-1)
  cases q
  · simp only [base, Bool.false_eq_true, if_false] at hh ⊢
    have hp := tail_pair_hinge u v
    have hzu := mul_nonneg (sub_nonneg.mpr hz.2) hu
    have hyv := mul_nonneg (sub_nonneg.mpr hy.2) hv
    nlinarith
  · simp only [base, if_true] at hh ⊢
    nlinarith

lemma coarse_hinge_polynomial (t y z : ℝ) (ht : t ∈ Set.Icc (1/2:ℝ) (2/3))
    (hy : y ∈ Set.Icc (0:ℝ) 1) (hz : z ∈ Set.Icc (0:ℝ) 1) :
    52/9 ≤ 19/9+8*t+(13/3-9*t)*y+(7/3-5*t)*z+y*z := by
  have h₀ : 0 ≤ (1/3:ℝ)-(y+z)/6+y*z := by
    have hp := mul_nonneg hy.1 hz.1
    linarith [hy.2,hz.2]
  have h₁ : 0 ≤ (1-y)*(5/3-z) := mul_nonneg (by linarith [hy.2]) (by linarith [hz.2])
  have ha : 0 ≤ 4-6*t := by linarith [ht.2]
  have hb : 0 ≤ 6*t-3 := by linarith [ht.1]
  have hh := add_nonneg (mul_nonneg ha h₀) (mul_nonneg hb h₁)
  nlinarith

/-- The13/54 estimate holds for all real counts satisfying these explicit
shared-branch, tail-mean and first-tail-hinge hypotheses. -/
theorem retained_mass_hinge_lower_bound {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (q : Ω → Bool)
    (ht : (∑ x, if q x then μ x else 0) ∈ Set.Icc (1/2:ℝ) (2/3))
    (y z : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) (hz : z ∈ Set.Icc (0:ℝ) 1)
    (u v d : Ω → ℝ) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hmu : (∑ x, μ x*u x) ≤ 1/3) (hmv : (∑ x, μ x*v x) ≤ 1/3)
    (hmd : (∑ x, μ x*d x) ≤ 2)
    (hhu : (∑ x, μ x*max 0 (u x-1)) ≤ 1/9)
    (hhv : (∑ x, μ x*max 0 (v x-1)) ≤ 1/9) :
    (13/54:ℝ) ≤ ∑ x, μ x*retention (base y (q x)+u x) (base z (q x)+v x) (d x) := by
  have hp := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (branch_hinge_minorant y z (u x) (v x) (d x)
      (q x) hy hz (hu x) (hv x)) (hμ x))
  have hcomp : (∑ x, μ x*(if q x then 0 else 1)) = 1-(∑ x, if q x then μ x else 0) := by
    have he (x : Ω) : μ x*(if q x then 0 else 1) = μ x-(if q x then μ x else 0) := by
      cases q x <;> simp
    simp_rw [he, Finset.sum_sub_distrib, hm]
  have he : (∑ x, μ x*((24-6*base y (q x)-4*base z (q x)+base y (q x)*base z (q x)-
      (5-z)*u x-(3-y)*v x-d x-(if q x then 0 else 1)-max 0 (u x-1)-max 0 (v x-1))/24)) =
      (24-6*(∑ x, μ x*base y (q x))-4*(∑ x, μ x*base z (q x))+
        (∑ x, μ x*(base y (q x)*base z (q x)))-
        (5-z)*(∑ x, μ x*u x)-(3-y)*(∑ x, μ x*v x)-(∑ x, μ x*d x)-
        (∑ x, μ x*(if q x then 0 else 1))-(∑ x, μ x*max 0 (u x-1))-
        (∑ x, μ x*max 0 (v x-1)))/24 := by
    conv_lhs =>
      arg 2
      ext x
      rw [show μ x*((24-6*base y (q x)-4*base z (q x)+base y (q x)*base z (q x)-
        (5-z)*u x-(3-y)*v x-d x-(if q x then 0 else 1)-max 0 (u x-1)-max 0 (v x-1))/24) =
        (24*μ x-6*(μ x*base y (q x))-4*(μ x*base z (q x))+
          μ x*(base y (q x)*base z (q x))-(5-z)*(μ x*u x)-(3-y)*(μ x*v x)-
          μ x*d x-μ x*(if q x then 0 else 1)-μ x*max 0 (u x-1)-μ x*max 0 (v x-1))/24 by ring]
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hm]
    ring
  rw [he, branch_mean μ q hm y, branch_mean μ q hm z,
    branch_product_mean μ q hm y z, hcomp] at hp
  have h₁ := mul_le_mul_of_nonneg_left hmu (by linarith [hz.2] : 0 ≤ 5-z)
  have h₂ := mul_le_mul_of_nonneg_left hmv (by linarith [hy.2] : 0 ≤ 3-y)
  have hh := coarse_hinge_polynomial _ y z ht hy hz
  nlinarith

lemma base_complement (y : ℝ) (b : Bool) : base (1-y) (!b) = base y b := by
  cases b <;> simp [base] <;> ring

/-- Either of the two surviving branches may initially have been named true. -/
theorem symmetric_retained_mass_hinge_lower_bound {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (q : Ω → Bool)
    (ht : (∑ x, if q x then μ x else 0) ∈ Set.Icc (1/3:ℝ) (2/3))
    (y z : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) (hz : z ∈ Set.Icc (0:ℝ) 1)
    (u v d : Ω → ℝ) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hmu : (∑ x, μ x*u x) ≤ 1/3) (hmv : (∑ x, μ x*v x) ≤ 1/3)
    (hmd : (∑ x, μ x*d x) ≤ 2)
    (hhu : (∑ x, μ x*max 0 (u x-1)) ≤ 1/9)
    (hhv : (∑ x, μ x*max 0 (v x-1)) ≤ 1/9) :
    (13/54:ℝ) ≤ ∑ x, μ x*retention (base y (q x)+u x) (base z (q x)+v x) (d x) := by
  by_cases hhalf : (1/2:ℝ) ≤ ∑ x, if q x then μ x else 0
  · exact retained_mass_hinge_lower_bound μ hμ hm q ⟨hhalf,ht.2⟩
      y z hy hz u v d hu hv hmu hmv hmd hhu hhv
  · have hcomp : (∑ x, if !q x then μ x else 0) = 1-(∑ x, if q x then μ x else 0) := by
      have he (x : Ω) : (if !q x then μ x else 0) = μ x-(if q x then μ x else 0) := by
        cases q x <;> simp
      simp_rw [he, Finset.sum_sub_distrib, hm]
    have hq : (∑ x, if !q x then μ x else 0) ∈ Set.Icc (1/2:ℝ) (2/3) := by
      rw [hcomp]
      constructor <;> linarith [ht.1]
    have hy' : 1-y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hy.2],by linarith [hy.1]⟩
    have hz' : 1-z ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hz.2],by linarith [hz.1]⟩
    have hh := retained_mass_hinge_lower_bound μ hμ hm (fun x => !q x) hq
      (1-y) (1-z) hy' hz' u v d hu hv hmu hmv hmd hhu hhv
    simpa only [base_complement] using hh

/-- Incomplete or averaged first-digit contributions may be majorized. -/
theorem dominated_retained_mass_hinge_lower_bound {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (q : Ω → Bool)
    (ht : (∑ x, if q x then μ x else 0) ∈ Set.Icc (1/3:ℝ) (2/3))
    (f g : Bool → ℝ) (hf : ∀ b, 0 ≤ f b) (hg : ∀ b, 0 ≤ g b)
    (hsf : f false+f true ≤ 1) (hsg : g false+g true ≤ 1)
    (a b u v d : Ω → ℝ) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (ha : ∀ x, a x ≤ 1+f (q x)+u x) (hb : ∀ x, b x ≤ 1+g (q x)+v x)
    (hmu : (∑ x, μ x*u x) ≤ 1/3) (hmv : (∑ x, μ x*v x) ≤ 1/3)
    (hmd : (∑ x, μ x*d x) ≤ 2)
    (hhu : (∑ x, μ x*max 0 (u x-1)) ≤ 1/9)
    (hhv : (∑ x, μ x*max 0 (v x-1)) ≤ 1/9) :
    (13/54:ℝ) ≤ ∑ x, μ x*retention (a x) (b x) (d x) := by
  obtain ⟨y,hy,hyf⟩ := exists_base_majorant f hf hsf
  obtain ⟨z,hz,hzg⟩ := exists_base_majorant g hg hsg
  apply (symmetric_retained_mass_hinge_lower_bound μ hμ hm q ht y z hy hz
    u v d hu hv hmu hmv hmd hhu hhv).trans
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hμ x)
  exact retention_antitone _ _ _ _ _ _
    (by linarith [ha x, hyf (q x)]) (by linarith [hb x, hzg (q x)]) le_rfl

/- A sharp four-point example for this ABSTRACT comparison. It is not an
arithmetic covering system or a counterexample to the original conjecture. -/
noncomputable def sharpMass : Fin 4 → ℝ := ![2/3,1/9,1/9,1/9]
def sharpBranch : Fin 4 → Bool := ![true,false,false,false]
noncomputable def sharpU : Fin 4 → ℝ := ![0,2,0,1]
noncomputable def sharpV : Fin 4 → ℝ := ![0,0,2,1]

lemma sharp_nonneg (x : Fin 4) : 0 ≤ sharpMass x ∧ 0 ≤ sharpU x ∧ 0 ≤ sharpV x := by
  fin_cases x <;> norm_num [sharpMass,sharpU,sharpV]

lemma sharp_moments :
    (∑ x, sharpMass x) = 1 ∧
    (∑ x, if sharpBranch x then sharpMass x else 0) = 2/3 ∧
    (∑ x, sharpMass x*sharpU x) = 1/3 ∧
    (∑ x, sharpMass x*sharpV x) = 1/3 ∧
    (∑ x, sharpMass x*max 0 (sharpU x-1)) = 1/9 ∧
    (∑ x, sharpMass x*max 0 (sharpV x-1)) = 1/9 := by
  norm_num [Fin.sum_univ_succ,sharpMass,sharpBranch,sharpU,sharpV]

lemma sharp_value :
    (∑ x, sharpMass x*retention (base 1 (sharpBranch x)+sharpU x)
      (base 1 (sharpBranch x)+sharpV x) 2) = 13/54 := by
  norm_num [Fin.sum_univ_succ,sharpMass,sharpBranch,sharpU,sharpV,base,retention]

#print axioms retained_mass_hinge_lower_bound
#print axioms symmetric_retained_mass_hinge_lower_bound
#print axioms dominated_retained_mass_hinge_lower_bound
#print axioms sharp_value
end Erdos7CoarseRootHingeRetention
