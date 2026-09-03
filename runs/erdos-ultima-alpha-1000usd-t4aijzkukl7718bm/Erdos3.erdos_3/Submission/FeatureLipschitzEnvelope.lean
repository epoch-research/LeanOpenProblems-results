import Submission.StrongQuadraticRegularity
import Submission.ClippedSumPerturbation

/-! Exact bounded Lipschitz factor representation of the convex feature-class
minimizers. A finite McShane envelope gives an explicit extension, preserving
the weighted-coordinate distance bound and all original function values. -/
namespace Erdos3FeatureLipschitzEnvelope
open Finset Erdos3ClippedWeakRegularity Erdos3BoundedFeatureClasses
  Erdos3ClippedSumPerturbation
open scoped BigOperators Classical
set_option maxHeartbeats 5000000

variable {I : Type*} [Fintype I]

noncomputable def weightedDistance (w : I → NNReal) (v u : I → ℝ) : ℝ :=
  ∑ i : I, (w i : ℝ)*|v i-u i|

lemma weightedDistance_nonneg (w : I → NNReal) (v u : I → ℝ) : 0 ≤ weightedDistance w v u := by
  apply sum_nonneg
  intro i _
  positivity

lemma weightedDistance_self (w : I → NNReal) (v : I → ℝ) : weightedDistance w v v = 0 := by
  simp [weightedDistance]

lemma weightedDistance_symm (w : I → NNReal) (v u : I → ℝ) :
    weightedDistance w v u = weightedDistance w u v := by
  simp only [weightedDistance,abs_sub_comm]

lemma weightedDistance_triangle (w : I → NNReal) (v u t : I → ℝ) :
    weightedDistance w v t ≤ weightedDistance w v u+weightedDistance w u t := by
  unfold weightedDistance
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro i _
  simpa only [mul_add] using mul_le_mul_of_nonneg_left (abs_sub_le (v i) (u i) (t i)) (w i).coe_nonneg

lemma weightedDistance_norm_le (w : I → NNReal) (v u : I → ℝ) :
    weightedDistance w v u ≤ (∑ i : I, (w i : ℝ))*‖v-u‖ := by
  unfold weightedDistance
  rw [sum_mul]
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (w i).coe_nonneg
  exact norm_le_pi_norm (v-u) i

variable {X : Type*} [Fintype X] [Nonempty X]

noncomputable def rawEnvelope (c : X → I → ℝ) (w : I → NNReal) (g : X → ℝ) (v : I → ℝ) : ℝ :=
  univ.inf' univ_nonempty (fun x : X ↦ g x+weightedDistance w v (c x))

lemma rawEnvelope_sub_le (c : X → I → ℝ) (w : I → NNReal) (g : X → ℝ) (v u : I → ℝ) :
    rawEnvelope c w g v ≤ rawEnvelope c w g u+weightedDistance w v u := by
  obtain ⟨x,hx,hmin⟩ := exists_mem_eq_inf' (univ_nonempty : (univ : Finset X).Nonempty)
    (fun x : X ↦ g x+weightedDistance w u (c x))
  change rawEnvelope c w g u = g x+weightedDistance w u (c x) at hmin
  calc
    _ ≤ g x+weightedDistance w v (c x) := inf'_le _ hx
    _ ≤ g x+(weightedDistance w v u+weightedDistance w u (c x)) :=
      add_le_add le_rfl (weightedDistance_triangle w v u (c x))
    _ = _ := by rw [hmin]; ring

lemma rawEnvelope_abs_sub (c : X → I → ℝ) (w : I → NNReal) (g : X → ℝ) (v u : I → ℝ) :
    |rawEnvelope c w g v-rawEnvelope c w g u| ≤ weightedDistance w v u := by
  have h₁ := rawEnvelope_sub_le c w g v u
  have h₂ := rawEnvelope_sub_le c w g u v
  rw [weightedDistance_symm w u v] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma rawEnvelope_on_coordinates (c : X → I → ℝ) (w : I → NNReal) (g : X → ℝ)
    (hg : ∀ x y, |g x-g y| ≤ weightedDistance w (c x) (c y)) (x : X) :
    rawEnvelope c w g (c x) = g x := by
  apply le_antisymm
  · have h := inf'_le (fun y : X ↦ g y+weightedDistance w (c x) (c y)) (mem_univ x)
    simpa only [weightedDistance_self,add_zero] using h
  · apply le_inf'
    intro y _
    have h := (abs_le.mp (hg x y)).2
    linarith

noncomputable def boundedEnvelope (c : X → I → ℝ) (w : I → NNReal) (g : X → ℝ) (v : I → ℝ) : ℝ :=
  clip01 (rawEnvelope c w g v)

lemma boundedEnvelope_bounds (c : X → I → ℝ) (w : I → NNReal) (g : X → ℝ) (v : I → ℝ) :
    0 ≤ boundedEnvelope c w g v ∧ boundedEnvelope c w g v ≤ 1 := clip01_bounds _

lemma boundedEnvelope_abs_sub (c : X → I → ℝ) (w : I → NNReal) (g : X → ℝ) (v u : I → ℝ) :
    |boundedEnvelope c w g v-boundedEnvelope c w g u| ≤ weightedDistance w v u :=
  (clip01_abs_sub _ _).trans (rawEnvelope_abs_sub c w g v u)

lemma boundedEnvelope_lipschitz (c : X → I → ℝ) (w : I → NNReal) (g : X → ℝ) :
    LipschitzWith (∑ i : I, w i) (boundedEnvelope c w g) := by
  apply LipschitzWith.of_dist_le_mul
  intro v u
  simp only [Real.dist_eq,dist_eq_norm,NNReal.coe_sum]
  exact (boundedEnvelope_abs_sub c w g v u).trans (weightedDistance_norm_le w v u)

lemma boundedEnvelope_on_coordinates (c : X → I → ℝ) (w : I → NNReal) (g : X → ℝ)
    (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hg : ∀ x y, |g x-g y| ≤ weightedDistance w (c x) (c y)) (x : X) :
    boundedEnvelope c w g (c x) = g x := by
  rw [boundedEnvelope,rawEnvelope_on_coordinates c w g hg,
    clip01,min_eq_right (hbound x).2,max_eq_right (hbound x).1]

/-- Every function in the bounded feature class has an exact global bounded
Lipschitz factor representation. The stronger weighted-distance estimate is
retained, allowing different error budgets for different coordinates. -/
theorem featureClass_factor {l : List (Feature X)} {g : X → ℝ} (hg : g ∈ featureClass l) :
    ∃ Φ : (Fin l.length → ℝ) → ℝ,
      (∀ v, 0 ≤ Φ v ∧ Φ v ≤ 1) ∧
      LipschitzWith (∑ i : Fin l.length, (l.get i).1) Φ ∧
      (∀ v u, |Φ v-Φ u| ≤ weightedDistance (fun i ↦ (l.get i).1) v u) ∧
      (∀ x, Φ (fun i ↦ (l.get i).2 x) = g x) := by
  let c : X → Fin l.length → ℝ := fun x i ↦ (l.get i).2 x
  let w : Fin l.length → NNReal := fun i ↦ (l.get i).1
  have hcontrol (x y : X) : |g x-g y| ≤ weightedDistance w (c x) (c y) := by
    have hh := hg.2 x y
    change |g x-g y| ≤ (l.map (fun p ↦ (p.1 : ℝ)*|p.2 x-p.2 y|)).sum at hh
    rw [list_sum_map_eq_sum_get] at hh
    exact hh
  exact ⟨boundedEnvelope c w g,boundedEnvelope_bounds c w g,boundedEnvelope_lipschitz c w g,
    boundedEnvelope_abs_sub c w g,boundedEnvelope_on_coordinates c w g hg.1 hcontrol⟩

#print axioms boundedEnvelope_lipschitz
#print axioms featureClass_factor
end Erdos3FeatureLipschitzEnvelope
