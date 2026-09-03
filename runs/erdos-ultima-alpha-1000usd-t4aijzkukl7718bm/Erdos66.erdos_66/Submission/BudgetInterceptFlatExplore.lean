import Submission.InterceptBudgetPointwiseExplore
import Submission.InterceptPrefixExplore

/-! Actual anchored graph counts with a uniformly controlled cubic correction.
The integer prefix is preserved, but no infinite-scale claim is made. -/
namespace Erdos66BudgetInterceptFlat
open Erdos66InterceptBudgetPointwise Erdos66InterceptGoodTranslation
  Erdos66InterceptCurve Erdos66InterceptCollisionCorrection Erdos66InterceptPrefix
  Erdos66InheritedOriginLift Erdos66OriginRepair Erdos66CrossGraph
  Erdos66TranslatedMixedFiber Erdos66TranslatedCharacterEnergy Erdos66MixedEnergy
open scoped Classical
set_option maxHeartbeats 2400000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
lemma admissible_of_outside_opposite (h2 : (2 : F)≠0) (U : Finset F) (a : F)
    (ha : a∉oppositeForbidden U) :
    (∀u∈translated U a,u≠0) ∧ ∀u∈translated U a,∀v∈translated U a,u+v≠0 := by
  obtain ⟨hz,ho⟩ := outside_opposite h2 U a ha
  constructor
  · intro u hu
    change u∈U.image (fun x ↦ a+x) at hu
    obtain ⟨u0,hu0,rfl⟩ := Finset.mem_image.mp hu
    exact hz u0 hu0
  · intro u hu v hv
    change u∈U.image (fun x ↦ a+x) at hu
    change v∈U.image (fun x ↦ a+x) at hv
    obtain ⟨u0,hu0,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v0,hv0,rfl⟩ := Finset.mem_image.mp hv
    exact ho u0 hu0 v0 hv0

lemma weighted_support_bound (hF : ringChar F≠2) (U S : Finset F)
    (hS : ∀u∈U,∀v∈U,u+v∈S) (a : F) (ha : a∉oppositeForbidden U)
    (hE : (translatedEnergy U a : ℝ) ≤ 16*(U.card : ℝ)^2) (q t : F) :
    |(weightedCount (translated U a) (translated U a) q t : ℝ)-(U.card : ℝ)^2| ≤
      Real.sqrt (16*(S.card : ℝ)*(U.card : ℝ)^2) := by
  obtain ⟨hU,hUU⟩ := admissible_of_outside_opposite (Ring.two_ne_zero hF) U a ha
  let T := S.image (fun s ↦ a+a+s)
  have hT : T.card=S.card := Finset.card_image_of_injective _ (add_right_injective _)
  have ht : ∀u∈translated U a,∀v∈translated U a,u+v∈T := by
    intro u hu v hv
    change u∈U.image (fun x ↦ a+x) at hu
    change v∈U.image (fun x ↦ a+x) at hv
    obtain ⟨u0,hu0,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v0,hv0,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨u0+v0,hS u0 hu0 v0 hv0,by ring⟩
  have hL := crossCharFiber_l1_sq_le (translated U a) (translated U a) T ht
  rw [hT,translated,energy_signed_translate] at hL
  have hL' := hL.trans (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg S.card))
  have hbound : (∑s : F, |(crossCharFiber (translated U a) (translated U a) s : ℝ)|) ≤
      Real.sqrt (16*(S.card : ℝ)*(U.card : ℝ)^2) := by
    apply (Real.le_sqrt (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) (by positivity)).mpr
    convert hL' using 1
    ring
  have hw := weightedCount_error hF (translated U a) (translated U a) hU hU hUU q t
  rw [translated_card] at hw
  have hw' : |(weightedCount (translated U a) (translated U a) q t : ℝ)-(U.card : ℝ)^2| ≤
      ∑s : F, |(crossCharFiber (translated U a) (translated U a) s : ℝ)| := by
    have hw'' : |weightedCount (translated U a) (translated U a) q t-(U.card : ℤ)^2| ≤
        ∑s : F, |crossCharFiber (translated U a) (translated U a) s| := by
      simpa only [pow_two] using hw
    exact_mod_cast hw''
  exact hw'.trans hbound

lemma actual_error_bound (hF : ringChar F≠2) (U S : Finset F)
    (hS : ∀u∈U,∀v∈U,u+v∈S) (a : F) (ha : a∉oppositeForbidden U)
    (hE : (translatedEnergy U a : ℝ) ≤ 16*(U.card : ℝ)^2) (z : F × F) :
    |(pairCount (curveUnion (translated U a)) (curveUnion (translated U a)) z : ℝ)-
      (U.card : ℝ)^2| ≤ Real.sqrt (16*(S.card : ℝ)*(U.card : ℝ)^2)+24*U.card+
        (correction U a z-24*U.card : ℕ) := by
  obtain ⟨t,q⟩ := z
  obtain ⟨hU,_⟩ := admissible_of_outside_opposite (Ring.two_ne_zero hF) U a ha
  have hw := weighted_support_bound hF U S hS a ha hE q t
  have he := weighted_set_correction (translated U a) hU q t
  have hc : (weightedCount (translated U a) (translated U a) q t : ℝ)-
      pairCount (curveUnion (translated U a)) (curveUnion (translated U a)) (t,q) =
      (correction U a (t,q) : ℝ) := by
    unfold correction
    push_cast
    linarith
  have hn : (correction U a (t,q) : ℝ) ≤
      24*U.card+(correction U a (t,q)-24*U.card : ℕ) := by
    exact_mod_cast (show correction U a (t,q) ≤ 24*U.card+(correction U a (t,q)-24*U.card) by omega)
  have htriangle := abs_sub_le
    (pairCount (curveUnion (translated U a)) (curveUnion (translated U a)) (t,q) : ℝ)
    (weightedCount (translated U a) (translated U a) q t : ℝ) ((U.card : ℝ)^2)
  have habs : |(pairCount (curveUnion (translated U a)) (curveUnion (translated U a)) (t,q) : ℝ)-
      (weightedCount (translated U a) (translated U a) q t : ℝ)| = (correction U a (t,q) : ℝ) := by
    rw [abs_sub_comm,hc,abs_of_nonneg (Nat.cast_nonneg _)]
  rw [habs] at htriangle
  linarith

/-- The correction `D` may depend on the target, but the cubic bound is
uniform. The row-zero identity is exact. -/
theorem exists_budget_anchored_graph (hF : ringChar F≠2) (U S : Finset F)
    (hS : ∀u∈U,∀v∈U,u+v∈S) (hU : 0 < U.card)
    (hsize : 2*U.card^2 < Fintype.card F) :
    ∃ (a : F) (D : F × F → ℕ),
      (∀x : F,(x,0)∈anchored U a ↔ x∈U) ∧
      ∀z : F × F,
        |(pairCount (anchored U a) (anchored U a) z : ℝ)-(U.card : ℝ)^2| ≤
          Real.sqrt (16*(S.card : ℝ)*(U.card : ℝ)^2)+24*U.card+D z ∧
        Fintype.card F*(D z)^3 ≤ 6912*U.card^9 := by
  obtain ⟨a,ha,hE,hC⟩ := exists_low_energy_pointwise hF U hU hsize
  let D : F × F → ℕ := fun z ↦ correction U a (z-(-a,0)-(-a,0))-24*U.card
  refine ⟨a,D,anchored_row_zero U a,fun z ↦ ⟨?_,hC _⟩⟩
  rw [anchored_pairCount]
  exact actual_error_bound hF U S hS a ha hE _

end Erdos66BudgetInterceptFlat
