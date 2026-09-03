import Submission.InterceptCollisionIncidenceExplore
import Submission.InterceptPrefixExplore

/-! Complete set-level flatness for intercept graphs, with an explicit
polynomial field-size cost and literal preservation of the old row. -/
namespace Erdos66GoodInterceptFlat
open Erdos66InterceptEdgePolynomial Erdos66InterceptConcurrencyPolynomial
  Erdos66InterceptGoodTranslation Erdos66InterceptCurve Erdos66InterceptCollisionCorrection
  Erdos66InterceptCollisionIncidence Erdos66InterceptPrefix Erdos66InheritedOriginLift
  Erdos66OriginRepair Erdos66CrossGraph Erdos66TranslatedMixedFiber Erdos66MixedEnergy
open scoped Classical
set_option maxHeartbeats 2400000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma good_collision_correction (h2 : (2 : F)≠0) (U : Finset F) (a : F)
    (ha : a∉allForbidden U) (q t : F) :
    |(pairCount (curveUnion (translated U a)) (curveUnion (translated U a)) (t,q) : ℝ)-
      (weightedCount (translated U a) (translated U a) q t : ℝ)|≤ 12*U.card := by
  obtain ⟨hU,_⟩ := outside_admissible h2 U a ha
  have he := weighted_set_correction (translated U a) hU q t
  have hc := collision_union_cap h2 U a ha (t,q)
  rw [pairCount_comm] at hc
  have hc' : (pairCount (curveUnion (translated U a)) (collisionSet (translated U a)) (t,q) : ℝ)≤ 4*U.card := by
    exact_mod_cast hc
  have hd' : (pairCount (collisionSet (translated U a)) (collisionSet (translated U a)) (t,q) : ℝ)≤ 4*U.card := by
    exact_mod_cast collision_self_cap h2 U a ha (t,q)
  have hn1 := Nat.cast_nonneg
    (pairCount (curveUnion (translated U a)) (collisionSet (translated U a)) (t,q)) (α := ℝ)
  have hn2 := Nat.cast_nonneg
    (pairCount (collisionSet (translated U a)) (collisionSet (translated U a)) (t,q)) (α := ℝ)
  rw [abs_le]
  constructor <;> linarith

lemma good_actual_error (hF : ringChar F≠2) (U : Finset F) (a : F)
    (ha : a∉allForbidden U) (z : F × F) :
    |(pairCount (curveUnion (translated U a)) (curveUnion (translated U a)) z : ℝ)-
      (U.card : ℝ)^2|≤ 
      (∑s : F, |(crossCharFiber (translated U a) (translated U a) s : ℝ)|)+12*U.card := by
  obtain ⟨t,q⟩ := z
  obtain ⟨hU,hUU⟩ := outside_admissible (Ring.two_ne_zero hF) U a ha
  have hw := weightedCount_error hF (translated U a) (translated U a) hU hU hUU q t
  have hw' : |(weightedCount (translated U a) (translated U a) q t : ℝ)-(U.card : ℝ)^2|≤ 
      ∑s : F, |(crossCharFiber (translated U a) (translated U a) s : ℝ)| := by
    rw [translated_card] at hw
    have hw'' : |weightedCount (translated U a) (translated U a) q t-(U.card : ℤ)^2|≤ 
        ∑s : F, |crossCharFiber (translated U a) (translated U a) s| := by
      simpa only [pow_two] using hw
    exact_mod_cast hw''
  have hc := good_collision_correction (Ring.two_ne_zero hF) U a ha q t
  have ht := abs_sub_le
    (pairCount (curveUnion (translated U a)) (curveUnion (translated U a)) (t,q) : ℝ)
    (weightedCount (translated U a) (translated U a) q t : ℝ) ((U.card : ℝ)^2)
  linarith

lemma good_error_with_support (hF : ringChar F≠2) (U S : Finset F)
    (hS : ∀u∈U,∀v∈U,u+v∈S) (a : F) (ha : a∉allForbidden U)
    (hE : energy (signedFunction (translated U a)) (signedFunction (translated U a))≤ 8*(U.card : ℝ)^2)
    (z : F × F) :
    |(pairCount (curveUnion (translated U a)) (curveUnion (translated U a)) z : ℝ)-(U.card : ℝ)^2|≤ 
      Real.sqrt (8*(S.card : ℝ)*(U.card : ℝ)^2)+12*U.card := by
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
  rw [hT] at hL
  have hL' := hL.trans (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg S.card))
  have hbound : (∑s : F, |(crossCharFiber (translated U a) (translated U a) s : ℝ)|)≤ 
      Real.sqrt (8*(S.card : ℝ)*(U.card : ℝ)^2) := by
    apply (Real.le_sqrt (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) (by positivity)).mpr
    convert hL' using 1
    ring
  have hh := good_actual_error hF U a ha z
  linarith

/-- All finite group targets are covered, including zero. This theorem does
not identify these counts with ordinary counts above the preserved prefix. -/
theorem exists_good_anchored_graph (hF : ringChar F≠2) (U S : Finset F)
    (hS : ∀u∈U,∀v∈U,u+v∈S) (hsize : 2*(8*U.card^7+U.card^2)<Fintype.card F) :
    ∃a : F, (∀x : F,(x,0)∈anchored U a ↔ x∈U) ∧
      ∀z : F × F, |(pairCount (anchored U a) (anchored U a) z : ℝ)-(U.card : ℝ)^2|≤ 
        Real.sqrt (8*(S.card : ℝ)*(U.card : ℝ)^2)+12*U.card := by
  obtain ⟨a,ha,_,_,hE⟩ := exists_good_low_energy_translate hF U hsize
  refine ⟨a,anchored_row_zero U a,?_⟩
  intro z
  rw [anchored_pairCount]
  exact good_error_with_support hF U S hS a ha hE _

end Erdos66GoodInterceptFlat
