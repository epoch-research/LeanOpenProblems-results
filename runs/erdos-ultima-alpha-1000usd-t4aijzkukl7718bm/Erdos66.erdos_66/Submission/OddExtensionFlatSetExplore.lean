import Submission.OddExtensionCharacterFiberExplore

/-! A repaired parabola union extends through odd-degree finite fields with
its old slice and error budget intact. The mean does not grow in this result. -/
namespace Erdos66OddExtensionFlatSet
open Erdos66OddFieldExtension Erdos66OddExtensionCharacterFiber
  Erdos66FiniteField Erdos66OriginRepair Erdos66ParabolaRepair Erdos66Coset
open scoped Classical
set_option maxHeartbeats 2200000

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]

def planeMap (z : F×F) : K×K := (algebraMap F K z.1,algebraMap F K z.2)

lemma planeMap_injective : Function.Injective (planeMap (F := F) (K := K)) := by
  intro x y h
  exact Prod.ext ((algebraMap F K).injective (congrArg Prod.fst h))
    ((algebraMap F K).injective (congrArg Prod.snd h))

lemma parabolaSet_old_slice (U : Finset F) (z : F×F) :
    planeMap z ∈ parabolaSet (U.image (algebraMap F K)) ↔ z∈parabolaSet U := by
  simp only [parabolaSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨u,⟨v,hv,rfl⟩,hz⟩
    refine ⟨v,hv,?_⟩
    exact (mem_curve _ _).mp ((curve_old_slice v z.1 z.2).mp ((mem_curve _ _).mpr hz))
  · rintro ⟨u,hu,hz⟩
    refine ⟨algebraMap F K u,⟨u,hu,rfl⟩,?_⟩
    exact (mem_curve _ _).mp ((curve_old_slice u z.1 z.2).mpr ((mem_curve _ _).mpr hz))

lemma partialCurve_map (w : F) (T : Finset F) :
    partialCurve (algebraMap F K w) (T.image (algebraMap F K))=
      (partialCurve w T).image (planeMap (K := K)) := by
  simp only [partialCurve,Finset.image_image,Function.comp_def,planeMap,map_div₀,map_pow]

lemma repairPoints_map (w : F) (T : Finset F) :
    repairPoints (algebraMap F K w) (T.image (algebraMap F K))=
      (repairPoints w T).image (planeMap (K := K)) := by
  simp only [repairPoints,partialCurve_map,Finset.image_union,Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro z hz
  simp [Function.comp_def,planeMap]

lemma repaired_old_slice (U : Finset F) (w : F) (T : Finset F) (z : F×F) :
    planeMap z ∈ parabolaSet (U.image (algebraMap F K)) ∪
      repairPoints (algebraMap F K w) (T.image (algebraMap F K)) ↔
    z∈parabolaSet U ∪ repairPoints w T := by
  rw [Finset.mem_union,Finset.mem_union,parabolaSet_old_slice,repairPoints_map]
  exact or_congr_right (Finset.mem_image.trans
    ⟨fun ⟨x,hx,he⟩ ↦ (planeMap_injective he) ▸ hx,fun hz ↦ ⟨z,hz,rfl⟩⟩)

/-- All target counts of the actual extended set retain the old budget.
The origin has its prescribed repaired value; every nonzero target is
within old character error plus 10|U|+8 of |U|^2. -/
theorem extended_repaired_counts (hd : Odd (Module.finrank F K)) (hK : ringChar K≠2)
    (U : Finset F) (hU : ∀ u∈U, u≠0)
    (hUU : ∀ u∈U, ∀ v∈U, u+v≠0) (hne : U.Nonempty)
    (w : F) (hw : w≠0) (hwU : w∉U) (hnwU : -w∉U)
    (T : Finset F) (hT : (0:F)∉T) :
    let B := parabolaSet (U.image (algebraMap F K)) ∪
      repairPoints (algebraMap F K w) (T.image (algebraMap F K))
    pairCount B B 0=1+2*T.card ∧
      ∀ z : K×K, z≠0 → |(pairCount B B z:ℤ)-(U.card:ℤ)^2|≤
        (∑ a : F, |charFiber U a|)+10*(U.card:ℤ)+8 := by
  let f := algebraMap F K
  let V := U.image f
  have hV : ∀ u∈V, u≠0 := by
    intro u hu
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    exact (map_ne_zero f).mpr (hU a ha)
  have hVV : ∀ u∈V, ∀ v∈V, u+v≠0 := by
    intro u hu v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    rw [←map_add]
    exact (map_ne_zero f).mpr (hUU a ha b hb)
  have hVne : V.Nonempty := hne.image f
  have hw' : f w≠0 := (map_ne_zero f).mpr hw
  have hwV : f w∉V := by simpa [V,Finset.mem_image,f.injective.eq_iff] using hwU
  have hnwV : -(f w)∉V := by
    intro hn
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hn
    have he' : f a=f (-w) := by simpa only [map_neg] using he
    exact hnwU ((f.injective he') ▸ ha)
  have hT' : (0:K)∉T.image f := by simpa [Finset.mem_image,map_eq_zero] using hT
  have hcard : V.card=U.card := Finset.card_image_of_injective _ f.injective
  obtain ⟨hz,hh⟩ := parabola_origin_repair hK V hV hVV hVne (f w) hw' hwV hnwV
    (T.image f) hT'
  dsimp only
  constructor
  · simpa only [Finset.card_image_of_injective _ f.injective] using hz
  · intro z hz0
    obtain ⟨hlo,hhi⟩ := hh z hz0
    have hb := graph_set_error_bound hK V hV hVV hVne z.1 z.2
      (by simpa only [Prod.mk.eta] using hz0)
    rw [←parabolaSet_pairCount_eq V z,hcard] at hb
    have hsum : (∑ a : K, |charFiber V a|)=∑ a : F, |charFiber U a| :=
      sum_abs_charFiber_map hd U
    rw [hsum] at hb
    have hlo' : (pairCount (parabolaSet V) (parabolaSet V) z:ℤ)≤
        pairCount (parabolaSet V∪repairPoints (f w) (T.image f))
          (parabolaSet V∪repairPoints (f w) (T.image f)) z := by exact_mod_cast hlo
    rw [hcard] at hhi
    have hhi' : (pairCount (parabolaSet V∪repairPoints (f w) (T.image f))
          (parabolaSet V∪repairPoints (f w) (T.image f)) z:ℤ)≤
        pairCount (parabolaSet V) (parabolaSet V) z+8*(U.card:ℤ)+8 := by exact_mod_cast hhi
    change |(pairCount (parabolaSet V∪repairPoints (f w) (T.image f))
      (parabolaSet V∪repairPoints (f w) (T.image f)) z:ℤ)-(U.card:ℤ)^2|≤_
    rw [abs_le] at hb ⊢
    constructor <;> omega

end Erdos66OddExtensionFlatSet
