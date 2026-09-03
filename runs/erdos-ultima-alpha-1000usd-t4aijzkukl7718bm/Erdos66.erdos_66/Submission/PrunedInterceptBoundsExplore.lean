import Submission.FinitePruningErrorExplore
import Submission.BudgetInterceptFlatExplore

/-! Propagating the energy and incidence budgets through pruning. The
original label count, rather than the pruned count, is retained as the mean. -/
namespace Erdos66PrunedInterceptBounds
open Erdos66FinitePruningError Erdos66InterceptOppositePruning
  Erdos66InterceptIncidenceBudget Erdos66InterceptBudgetPointwise
  Erdos66InterceptCurve Erdos66InterceptCollisionCorrection
  Erdos66InheritedOriginLift Erdos66OriginRepair Erdos66CrossGraph
  Erdos66TranslatedMixedFiber Erdos66TranslatedCharacterEnergy Erdos66MixedEnergy
open scoped Classical
set_option maxHeartbeats 2800000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
lemma translated_mono {U V : Finset F} (h : V⊆U) (a : F) : translated V a ⊆ translated U a :=
  Finset.image_subset_image h

lemma l1_from_energy (U S : Finset F) (hS : ∀u∈U,∀v∈U,u+v∈S)
    (a : F) (hE : (translatedEnergy U a : ℝ) ≤ 12*(U.card : ℝ)^2) :
    (∑s : F, |(crossCharFiber (translated U a) (translated U a) s : ℝ)|) ≤
      Real.sqrt (12*(S.card : ℝ)*(U.card : ℝ)^2) := by
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
  have hh := hL.trans (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg S.card))
  apply (Real.le_sqrt (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) (by positivity)).mpr
  convert hh using 1
  ring

lemma pruned_l1_bound (U S : Finset F) (hS : ∀u∈U,∀v∈U,u+v∈S)
    (a : F) (hE : (translatedEnergy U a : ℝ) ≤ 12*(U.card : ℝ)^2) :
    (∑s : F, |(crossCharFiber (translated (pruned U a) a) (translated (pruned U a) a) s : ℝ)|) ≤
      Real.sqrt (12*(S.card : ℝ)*(U.card : ℝ)^2)+2*U.card*oppositeCount U a := by
  have hh := crossCharFiber_pruning (translated U a) (translated (pruned U a) a)
    (translated_mono (pruned_subset U a) a)
  rw [translated_card,translated_card] at hh
  have hloss := square_card_loss U (pruned U a) (pruned_subset U a) (oppositeCount U a)
    (pruned_card_loss U a)
  have hl : (∑s : F, |(crossCharFiber (translated (pruned U a) a) (translated (pruned U a) a) s : ℝ)|) ≤
      (∑s : F, |(crossCharFiber (translated U a) (translated U a) s : ℝ)|)+
        (U.card^2-(pruned U a).card^2 : ℕ) := by exact_mod_cast hh
  have hc : ((U.card^2-(pruned U a).card^2 : ℕ) : ℝ) ≤ 2*U.card*oppositeCount U a := by
    exact_mod_cast hloss
  have he := l1_from_energy U S hS a hE
  linarith

lemma mean_loss (U : Finset F) (a : F) :
    |((pruned U a).card : ℝ)^2-(U.card : ℝ)^2| ≤ 2*U.card*oppositeCount U a := by
  have hc := Finset.card_le_card (pruned_subset U a)
  have hp := Nat.pow_le_pow_left hc 2
  have hh := square_card_loss U (pruned U a) (pruned_subset U a) (oppositeCount U a)
    (pruned_card_loss U a)
  have hh' : (U.card : ℝ)^2-((pruned U a).card : ℝ)^2 ≤ 2*U.card*oppositeCount U a := by
    exact_mod_cast (show (U.card^2 : ℤ)-(pruned U a).card^2 ≤ 2*U.card*oppositeCount U a by
      exact_mod_cast hh)
  have hp' : ((pruned U a).card : ℝ)^2 ≤ (U.card : ℝ)^2 := by exact_mod_cast hp
  rwa [abs_of_nonpos (sub_nonpos.mpr hp'),neg_sub]

lemma pruned_weighted_bound (hF : ringChar F≠2) (U S : Finset F)
    (hS : ∀u∈U,∀v∈U,u+v∈S) (a : F)
    (hE : (translatedEnergy U a : ℝ) ≤ 12*(U.card : ℝ)^2) (q t : F) :
    |(weightedCount (translated (pruned U a) a) (translated (pruned U a) a) q t : ℝ)-
      (U.card : ℝ)^2| ≤ Real.sqrt (12*(S.card : ℝ)*(U.card : ℝ)^2)+4*U.card*oppositeCount U a := by
  obtain ⟨hz,ho⟩ := pruned_admissible (Ring.two_ne_zero hF) U a
  have hw := weightedCount_error hF _ _ hz hz ho q t
  rw [translated_card] at hw
  have hw' : |(weightedCount (translated (pruned U a) a) (translated (pruned U a) a) q t : ℝ)-
      ((pruned U a).card : ℝ)^2| ≤
      ∑s : F, |(crossCharFiber (translated (pruned U a) a) (translated (pruned U a) a) s : ℝ)| := by
    have hw'' : |weightedCount (translated (pruned U a) a) (translated (pruned U a) a) q t-
        ((pruned U a).card : ℤ)^2| ≤
        ∑s : F, |crossCharFiber (translated (pruned U a) a) (translated (pruned U a) a) s| := by
      simpa only [pow_two] using hw
    exact_mod_cast hw''
  have hl := pruned_l1_bound U S hS a hE
  have hm := mean_loss U a
  have ht := abs_sub_le
    (weightedCount (translated (pruned U a) a) (translated (pruned U a) a) q t : ℝ)
    (((pruned U a).card : ℝ)^2) ((U.card : ℝ)^2)
  linarith

lemma pruned_actual_bound (hF : ringChar F≠2) (U S : Finset F)
    (hS : ∀u∈U,∀v∈U,u+v∈S) (a : F)
    (hE : (translatedEnergy U a : ℝ) ≤ 12*(U.card : ℝ)^2) (z : F × F) :
    |(pairCount (curveUnion (translated (pruned U a) a)) (curveUnion (translated (pruned U a) a)) z : ℝ)-
      (U.card : ℝ)^2| ≤ Real.sqrt (12*(S.card : ℝ)*(U.card : ℝ)^2)+4*U.card*oppositeCount U a+
        24*U.card+(correction (pruned U a) a z-24*U.card : ℕ) := by
  obtain ⟨t,q⟩ := z
  have hz := (pruned_admissible (Ring.two_ne_zero hF) U a).1
  have hw := pruned_weighted_bound hF U S hS a hE q t
  have he := weighted_set_correction (translated (pruned U a) a) hz q t
  have hc : (weightedCount (translated (pruned U a) a) (translated (pruned U a) a) q t : ℝ)-
      pairCount (curveUnion (translated (pruned U a) a)) (curveUnion (translated (pruned U a) a)) (t,q) =
      (correction (pruned U a) a (t,q) : ℝ) := by
    unfold correction
    push_cast
    linarith
  have hn : (correction (pruned U a) a (t,q) : ℝ) ≤
      24*U.card+(correction (pruned U a) a (t,q)-24*U.card : ℕ) := by
    exact_mod_cast (show correction (pruned U a) a (t,q) ≤
      24*U.card+(correction (pruned U a) a (t,q)-24*U.card) by omega)
  have ht := abs_sub_le
    (pairCount (curveUnion (translated (pruned U a) a)) (curveUnion (translated (pruned U a) a)) (t,q) : ℝ)
    (weightedCount (translated (pruned U a) a) (translated (pruned U a) a) q t : ℝ) ((U.card : ℝ)^2)
  have habs : |(pairCount (curveUnion (translated (pruned U a) a))
      (curveUnion (translated (pruned U a) a)) (t,q) : ℝ)-
      (weightedCount (translated (pruned U a) a) (translated (pruned U a) a) q t : ℝ)| =
      (correction (pruned U a) a (t,q) : ℝ) := by
    rw [abs_sub_comm,hc,abs_of_nonneg (Nat.cast_nonneg _)]
  rw [habs] at ht
  linarith

lemma pruned_correction_cubic (hF : ringChar F≠2) (U : Finset F) (a : F) (z : F × F) :
    (correction (pruned U a) a z-24*U.card)^3 ≤ 216*U.card^2*budget U a := by
  have hc := Finset.card_le_card (pruned_subset U a)
  have hs : correction (pruned U a) a z-24*U.card ≤
      correction (pruned U a) a z-24*(pruned U a).card := Nat.sub_le_sub_left (Nat.mul_le_mul_left _ hc) _
  have hb := correction_cubic (pruned U a) a (pruned_admissible (Ring.two_ne_zero hF) U a).1 z
  calc
    _ ≤ (correction (pruned U a) a z-24*(pruned U a).card)^3 := Nat.pow_le_pow_left hs 3
    _ ≤ 216*(pruned U a).card^2*budget (pruned U a) a := hb
    _ ≤ 216*U.card^2*budget U a := Nat.mul_le_mul
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 2)) (budget_mono (pruned_subset U a) a)

end Erdos66PrunedInterceptBounds
