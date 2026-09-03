import Submission.CommonOriginFamilyExplore
import Submission.SharedParameterRootExplore

/-! Conversion of shared-parameter product-parabola counts to actual set
counts. The origin is not repaired in this file. -/
namespace Erdos66SharedParameterSet
open Erdos66CommonOriginFamily Erdos66OriginRepair Erdos66ParabolaRepair
  Erdos66SharedParameterRoot Erdos66FiniteField Erdos66CyclicVariance
open scoped Classical
set_option maxHeartbeats 1000000

section ProductCount
variable {G H : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup H] [DecidableEq H]
lemma pairCount_product (A B : Finset G) (C D : Finset H) (z : G) (w : H) :
    pairCount (A ×ˢ C) (B ×ˢ D) (z,w) = pairCount A B z*pairCount C D w := by
  unfold pairCount
  have he : ((A ×ˢ C).filter (fun x ↦ (z,w)-x∈B ×ˢ D)) =
      (A.filter (fun x ↦ z-x∈B)) ×ˢ (C.filter (fun y ↦ w-y∈D)) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_product,Prod.fst_sub,Prod.snd_sub]
    tauto
  rw [he,Finset.card_product]
end ProductCount

variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [DecidableEq K]

noncomputable def productCurve (u : F) (v : K) : Finset ((F × F) × (K × K)) :=
  curve u ×ˢ curve v

noncomputable def sharedSet (h : ℕ) (u : ℕ → F) (v : ℕ → K) :
    Finset ((F × F) × (K × K)) :=
  (Finset.range h).biUnion (fun i ↦ productCurve (u i) (v i))

lemma productCurve_zero (u : F) (v : K) : (0 : (F × F) × (K × K))∈productCurve u v := by
  simp [productCurve,mem_curve]

lemma sharedSet_zero (h : ℕ) (hh : 0<h) (u : ℕ → F) (v : ℕ → K) :
    (0 : (F × F) × (K × K))∈sharedSet h u v :=
  Finset.mem_biUnion.mpr ⟨0,Finset.mem_range.mpr hh,productCurve_zero _ _⟩

lemma productCurve_intersection (h : ℕ) (u : ℕ → F) (v : ℕ → K)
    (hu : ∀ i<h, u i ≠ 0) (hv : ∀ i<h, v i ≠ 0)
    (hiu : Set.InjOn u (Finset.range h)) (hiv : Set.InjOn v (Finset.range h))
    {i j : ℕ} (hi : i<h) (hj : j<h) (hij : i ≠ j)
    {z : (F × F) × (K × K)} (hzi : z∈productCurve (u i) (v i))
    (hzj : z∈productCurve (u j) (v j)) : z=0 := by
  obtain ⟨hziF,hziK⟩ := Finset.mem_product.mp hzi
  obtain ⟨hzjF,hzjK⟩ := Finset.mem_product.mp hzj
  have huv : u i ≠ u j := fun he ↦ hij (hiu (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) he)
  have hvv : v i ≠ v j := fun he ↦ hij (hiv (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) he)
  exact Prod.ext (curve_intersection (hu i hi) (hu j hj) huv hziF hzjF)
    (curve_intersection (hv i hi) (hv j hj) hvv hziK hzjK)

lemma productCurve_pairCount (u u' : F) (v v' : K) (z : (F × F) × (K × K)) :
    (pairCount (productCurve u v) (productCurve u' v') z : ℝ) =
      (Fintype.card {x : F // x^2/u+(z.1.1-x)^2/u'=z.1.2} : ℝ)*
      (Fintype.card {x : K // x^2/v+(z.2.1-x)^2/v'=z.2.2} : ℝ) := by
  obtain ⟨⟨t,s⟩,⟨t',s'⟩⟩ := z
  rw [productCurve,productCurve,pairCount_product,curve_pairCount,curve_pairCount,Nat.cast_mul]

/-- At nonzero targets the weighted-to-set correction is at most 2h. At
zero there is an additional quadratic origin mass. -/
theorem sharedSet_correction (h : ℕ) (hh : 0<h) (u : ℕ → F) (v : ℕ → K)
    (hu : ∀ i<h, u i ≠ 0) (hv : ∀ i<h, v i ≠ 0)
    (hiu : Set.InjOn u (Finset.range h)) (hiv : Set.InjOn v (Finset.range h))
    (z : (F × F) × (K × K)) :
    sharedRootCount h u v z.1.1 z.1.2 z.2.1 z.2.2 =
      (pairCount (sharedSet h u v) (sharedSet h u v) z : ℝ)+
        2*((h : ℝ)-1)*indicator (sharedSet h u v) z+
        ((h : ℝ)-1)^2*(if z=0 then 1 else 0) := by
  have he := common_origin_correction (Finset.range h) (fun i ↦ productCurve (u i) (v i))
    ⟨0,Finset.mem_range.mpr hh⟩ (fun i hi ↦ productCurve_zero _ _)
    (fun i hi j hj hij z hzi hzj ↦ productCurve_intersection h u v hu hv hiu hiv
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij hzi hzj) z
  simpa only [sharedRootCount,sharedSet,Finset.card_range,productCurve_pairCount] using he

theorem sharedSet_nonzero_error (h : ℕ) (hh : 0<h) (u : ℕ → F) (v : ℕ → K)
    (hu : ∀ i<h, u i ≠ 0) (hv : ∀ i<h, v i ≠ 0)
    (hiu : Set.InjOn u (Finset.range h)) (hiv : Set.InjOn v (Finset.range h))
    (z : (F × F) × (K × K)) (hz : z ≠ 0) :
    |(pairCount (sharedSet h u v) (sharedSet h u v) z : ℝ)-(h : ℝ)^2| ≤
      |sharedRootCount h u v z.1.1 z.1.2 z.2.1 z.2.2-(h : ℝ)^2|+2*h := by
  have he := sharedSet_correction h hh u v hu hv hiu hiv z
  rw [if_neg hz,mul_zero,add_zero] at he
  have hnon : (0 : ℝ) ≤ (h : ℝ)-1 := by exact_mod_cast (show 0 ≤ (h : ℤ)-1 by omega)
  have hI : 0 ≤ indicator (sharedSet h u v) z ∧ indicator (sharedSet h u v) z ≤ 1 := by
    unfold indicator
    split_ifs <;> norm_num
  have hcost : |2*((h : ℝ)-1)*indicator (sharedSet h u v) z| ≤ 2*h := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hnon) hI.1)]
    nlinarith [mul_le_mul_of_nonneg_left hI.2 (by positivity : (0 : ℝ) ≤ 2*((h : ℝ)-1))]
  have he' : (pairCount (sharedSet h u v) (sharedSet h u v) z : ℝ)-(h : ℝ)^2 =
      (sharedRootCount h u v z.1.1 z.1.2 z.2.1 z.2.2-(h : ℝ)^2)-
        2*((h : ℝ)-1)*indicator (sharedSet h u v) z := by linarith
  rw [he']
  exact (abs_sub _ _).trans (add_le_add le_rfl hcost)

lemma sharedRootCount_zero (h : ℕ) (u : ℕ → F) (v : ℕ → K)
    (hF : ringChar F ≠ 2) (hK : ringChar K ≠ 2)
    (hu : ∀ i<h, u i ≠ 0) (hv : ∀ i<h, v i ≠ 0)
    (huu : ∀ i<h, ∀ j<h, u i+u j ≠ 0) (hvv : ∀ i<h, ∀ j<h, v i+v j ≠ 0) :
    sharedRootCount h u v 0 0 0 0 = (h : ℝ)^2 := by
  unfold sharedRootCount
  have hcF (i j : ℕ) (hi : i<h) (hj : j<h) :
      (Fintype.card {x : F // x^2/u i+(0-x)^2/u j=0} : ℝ) = 1 := by
    have he := parabola_sum_count hF (u i) (u j) 0 0 (hu i hi) (hu j hj) (huu i hi j hj)
    norm_num at he
    simp only [zero_sub,neg_sq]
    exact_mod_cast he
  have hcK (i j : ℕ) (hi : i<h) (hj : j<h) :
      (Fintype.card {x : K // x^2/v i+(0-x)^2/v j=0} : ℝ) = 1 := by
    have he := parabola_sum_count hK (v i) (v j) 0 0 (hv i hi) (hv j hj) (hvv i hi j hj)
    norm_num at he
    simp only [zero_sub,neg_sq]
    exact_mod_cast he
  have he : (∑ i∈Finset.range h, ∑ j∈Finset.range h,
      (Fintype.card {x : F // x^2/u i+(0-x)^2/u j=0} : ℝ)*
      (Fintype.card {x : K // x^2/v i+(0-x)^2/v j=0} : ℝ)) =
        ∑ _i∈Finset.range h, ∑ _j∈Finset.range h, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcF i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj),
      hcK i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj),one_mul]
  rw [he]
  simp [pow_two]

theorem sharedSet_origin (h : ℕ) (hh : 0<h) (u : ℕ → F) (v : ℕ → K)
    (hF : ringChar F ≠ 2) (hK : ringChar K ≠ 2)
    (hu : ∀ i<h, u i ≠ 0) (hv : ∀ i<h, v i ≠ 0)
    (huu : ∀ i<h, ∀ j<h, u i+u j ≠ 0) (hvv : ∀ i<h, ∀ j<h, v i+v j ≠ 0)
    (hiu : Set.InjOn u (Finset.range h)) (hiv : Set.InjOn v (Finset.range h)) :
    pairCount (sharedSet h u v) (sharedSet h u v) 0 = 1 := by
  have he := sharedSet_correction h hh u v hu hv hiu hiv 0
  simp only [Prod.fst_zero,Prod.snd_zero] at he
  rw [sharedRootCount_zero h u v hF hK hu hv huu hvv] at he
  simp only [indicator,if_pos (sharedSet_zero h hh u v),ite_true,mul_one] at he
  have hh' : (pairCount (sharedSet h u v) (sharedSet h u v) 0 : ℝ) = 1 := by nlinarith
  exact_mod_cast hh'

end Erdos66SharedParameterSet
