import Submission.FirstRowFixingShearExplore
import Submission.CenteredMixedEnergyExplore

/-! Centered-energy control of spatially weighted shear averages. These
bounds concern the average over the shear parameter, not one simultaneous
choice of that parameter at every target. -/
namespace Erdos66WeightedShearEnergy
open Erdos66OriginRepair Erdos66ShearedParabolaPrefix Erdos66FirstRowFixingShear
  Erdos66MixedEnergy Erdos66CyclicVariance Erdos66CenteredMixedEnergy
open scoped Classical
set_option maxHeartbeats 1800000

section Group
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma weighted_sum_pairs (A B : Finset G) (w : G → ℝ) :
    (∑ a ∈ A, ∑ b ∈ B, w (a+b)) =
      ∑ z : G, w z * (pairCount A B z : ℝ) := by
  unfold pairCount
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [← Equiv.sum_comp (Equiv.addLeft a)]
  simp only [Equiv.coe_addLeft,add_sub_cancel_left,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_mem,Finset.univ_inter]

lemma conv_pairCount (A B : Finset G) (z : G) :
    conv (indicator A) (indicator B) z = (pairCount A B z : ℝ) := by
  rw [conv_indicators]
  unfold pairCount
  congr 2
  ext x
  simp only [Finset.mem_filter]

lemma weighted_mass_error_sq (A B : Finset G) (w : G → ℝ) (a b E D : ℝ)
    (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hA : ∀ z : G, |(pairCount A A z : ℝ)-a| ≤ E)
    (hB : ∀ z : G, |(pairCount B B z : ℝ)-b| ≤ D) :
    ((∑ x ∈ A, ∑ y ∈ B, w (x+y)) -
      (A.card : ℝ)*B.card/Fintype.card G * (∑ z : G, w z))^2 ≤
        (∑ z : G, w z^2) * (Fintype.card G : ℝ)*E*D := by
  have hm := mixed_centeredEnergy_le (indicator A) (indicator B) a b E D hE hD
    (by simpa only [conv_pairCount] using hA)
    (by simpa only [conv_pairCount] using hB)
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w
    (fun z ↦ (pairCount A B z : ℝ)-(A.card : ℝ)*B.card/Fintype.card G)
  have he : (∑ z : G, w z*((pairCount A B z : ℝ)-
        (A.card : ℝ)*B.card/Fintype.card G)) =
      (∑ x ∈ A, ∑ y ∈ B, w (x+y)) -
        (A.card : ℝ)*B.card/Fintype.card G * (∑ z : G, w z) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← weighted_sum_pairs,← Finset.sum_mul]
    ring
  rw [he] at hh
  have hm' : (∑ z : G, ((pairCount A B z : ℝ)-
      (A.card : ℝ)*B.card/Fintype.card G)^2) ≤ (Fintype.card G : ℝ)*E*D := by
    simpa only [centeredEnergy,conv_pairCount,mixedMean,sum_indicator] using hm
  exact hh.trans (by
    have h := mul_le_mul_of_nonneg_left hm' (Finset.sum_nonneg (s := Finset.univ) (fun z _ ↦ sq_nonneg (w z)))
    simpa only [mul_assoc] using h)

omit [Fintype G] in
lemma self_bound_image (e : G ≃+ G) (A : Finset G) (a E : ℝ)
    (hA : ∀ z : G, |(pairCount A A z : ℝ)-a| ≤ E) :
    ∀ z : G, |(pairCount (A.image e) (A.image e) z : ℝ)-a| ≤ E := by
  intro z
  obtain ⟨z,rfl⟩ := e.surjective z
  rw [pairCount_addEquiv]
  exact hA z

end Group

section Field
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def scaleAddEquiv (c : F) (hc : c ≠ 0) : F ≃+ F :=
  { Equiv.mulLeft₀ c hc with map_add' := fun x y ↦ mul_add c x y }

/-- Nonzero row heights turn the residual spatial weight into a mixed
convolution of two invertible dilations. Centered self-errors, rather than
uncentered energies, control its deviation from the uniform spatial mean. -/
theorem weighted_row_shear_error_sq (A B : Finset F) (y v t : F)
    (hy : y ≠ 0) (hv : v ≠ 0) (hs : y+v ≠ 0) (w : F → ℝ)
    (a b E D : ℝ) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hA : ∀ z : F, |(pairCount A A z : ℝ)-a| ≤ E)
    (hB : ∀ z : F, |(pairCount B B z : ℝ)-b| ≤ D) :
    ((∑ c : F, weightedPair
        (Erdos66PrefixFaithfulParabolaLift.shiftSet A (c*y))
        (Erdos66PrefixFaithfulParabolaLift.shiftSet B (c*v)) t w) -
      (A.card : ℝ)*B.card/Fintype.card F * (∑ z : F, w z))^2 ≤
        (∑ z : F, w z^2) * (Fintype.card F : ℝ)*E*D := by
  let e := scaleAddEquiv (v/(y+v)) (div_ne_zero hv hs)
  let f := scaleAddEquiv (-y/(y+v)) (div_ne_zero (neg_ne_zero.mpr hy) hs)
  let w' : F → ℝ := fun z ↦ w (z+y*t/(y+v))
  have hsum : (∑ z : F, w' z) = ∑ z : F, w z := by
    exact Equiv.sum_comp (Equiv.addRight (y*t/(y+v))) w
  have hsq : (∑ z : F, w' z^2) = ∑ z : F, w z^2 := by
    exact Equiv.sum_comp (Equiv.addRight (y*t/(y+v))) (fun z ↦ w z^2)
  have hecard : (A.image e).card = A.card := Finset.card_image_of_injective _ e.injective
  have hfcard : (B.image f).card = B.card := Finset.card_image_of_injective _ f.injective
  have hh := weighted_mass_error_sq (A.image e) (B.image f) w' a b E D hE hD
    (self_bound_image e A a E hA) (self_bound_image f B b D hB)
  rw [hecard,hfcard,hsum,hsq] at hh
  rw [weighted_row_shear_average A B y v t hs]
  convert hh using 2
  rw [Finset.sum_image (fun _ _ _ _ h ↦ e.injective h)]
  simp_rw [Finset.sum_image (fun _ _ _ _ h ↦ f.injective h)]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro z hz
  dsimp [w',e,f,scaleAddEquiv]
  congr 1
  field_simp
  ring

/-- Bounded spatial weights give an absolute error at most sqrt(E*D)
after averaging. The bound is uniform in both nonzero row heights. -/
theorem normalized_weighted_row_shear_error_sq (A B : Finset F) (y v t : F)
    (hy : y ≠ 0) (hv : v ≠ 0) (hs : y+v ≠ 0) (w : F → ℝ)
    (hw : ∀ z : F, 0 ≤ w z ∧ w z ≤ 1)
    (a b E D : ℝ) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hA : ∀ z : F, |(pairCount A A z : ℝ)-a| ≤ E)
    (hB : ∀ z : F, |(pairCount B B z : ℝ)-b| ≤ D) :
    ((∑ c : F, weightedPair
        (Erdos66PrefixFaithfulParabolaLift.shiftSet A (c*y))
        (Erdos66PrefixFaithfulParabolaLift.shiftSet B (c*v)) t w) /
          (Fintype.card F : ℝ) -
      ((A.card : ℝ)*B.card/Fintype.card F * (∑ z : F, w z)) /
          (Fintype.card F : ℝ))^2 ≤ E*D := by
  have hh := weighted_row_shear_error_sq A B y v t hy hv hs w a b E D hE hD hA hB
  have hw' : (∑ z : F, w z^2) ≤ (Fintype.card F : ℝ) := by
    calc
      _ ≤ ∑ _z : F, (1 : ℝ) := Finset.sum_le_sum (fun z _ ↦ by
        obtain ⟨h0,h1⟩ := hw z
        nlinarith)
      _ = _ := by simp
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hmul := mul_le_mul_of_nonneg_right hw' (show (0 : ℝ) ≤
      (Fintype.card F : ℝ)*E*D by positivity)
  rw [← sub_div,div_pow]
  apply (div_le_iff₀ (pow_pos hq 2)).mpr
  nlinarith only [hh,hmul]

end Field
end Erdos66WeightedShearEnergy
