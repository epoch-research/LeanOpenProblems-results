import Submission.AlignedProductRepairExplore
import Submission.SharedParameterSelectionExplore

/-! A genuine flat set in a product of two finite-field planes using shared
parameter labels. Its representation scale is h², not h⁴. This does not
provide compatible subsets of the natural numbers. -/
namespace Erdos66SharedParameterFlatSet
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66SharedParameterSet
  Erdos66ProductProjectionRepair Erdos66AlignedProductRepair
  Erdos66SharedParameterSelection Erdos66SharedParameterRoot
  Erdos66PolynomialMixedEnergy
open scoped Classical
set_option maxHeartbeats 1500000

lemma total_error_sq (h r b a : ℝ) (hh : 1 ≤ h)
    (hr : (r-h^2)^2 ≤ 432*h^3) (hb : |b-h^2| ≤ |r-h^2|+2*h)
    (hlo : b ≤ a) (hhi : a ≤ b+8*h+8) : (a-h^2)^2 ≤ 1512*h^3 := by
  have hcost : |a-b| ≤ 8*h+8 := by rw [abs_of_nonneg (sub_nonneg.mpr hlo)]; linarith
  have ha : |a-h^2| ≤ |r-h^2|+18*h := by
    have he := abs_sub_le a b (h^2)
    linarith
  have hsq := (sq_le_sq₀ (abs_nonneg (a-h^2)) (by positivity : 0 ≤ |r-h^2|+18*h)).mpr ha
  rw [sq_abs] at hsq
  have hp : h^2 ≤ h^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg h)]
  nlinarith [sq_nonneg (|r-h^2|-18*h),sq_abs (r-h^2)]

/-- A shared-parameter product produces an actual set, including an origin
repair, with uniformly vanishing relative error as h tends to infinity. -/
theorem exists_shared_flat_set (p q h : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hh : 0<h) (hp : max (8*h) (h^2/2) < p) (hq : max (8*h) (h^2/2) < q) :
    ∃ A : Finset ((ZMod p × ZMod p) × (ZMod q × ZMod q)), ∀ z,
      ((pairCount A A z : ℝ)-(h : ℝ)^2)^2 ≤ 1512*(h : ℝ)^3 := by
  have hp8 : 8*h<p := lt_of_le_of_lt (le_max_left _ _) hp
  have hq8 : 8*h<q := lt_of_le_of_lt (le_max_left _ _) hq
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hF : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  have hK : ringChar (ZMod q) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hq2
  obtain ⟨a,b,ha,hb,haa,hbb,hf,hg,hfg⟩ := exists_shared_low_energy p q h hh hp8 hq8
  let u : ℕ → ZMod p := fun i ↦ a+i
  let v : ℕ → ZMod q := fun i ↦ b+i
  have hiu : Set.InjOn u (Finset.range h) := by
    intro i hi j hj he
    exact natCast_injOn_range p h (by omega) hi hj (add_left_cancel he)
  have hiv : Set.InjOn v (Finset.range h) := by
    intro i hi j hj he
    exact natCast_injOn_range q h (by omega) hi hj (add_left_cancel he)
  have hcU : ((Finset.range h).image u).card ≤ h := Finset.card_image_le.trans_eq (Finset.card_range _)
  have hcV : ((Finset.range h).image v).card ≤ h := Finset.card_image_le.trans_eq (Finset.card_range _)
  obtain ⟨w,hw,hwU,hnwU⟩ := exists_unused_parameter ((Finset.range h).image u) (by rw [ZMod.card]; omega)
  obtain ⟨w',hw',hwV,hnwV⟩ := exists_unused_parameter ((Finset.range h).image v) (by rw [ZMod.card]; omega)
  let m := h^2/2
  have hmp : m<p := lt_of_le_of_lt (le_max_right _ _) hp
  have hmq : m<q := lt_of_le_of_lt (le_max_right _ _) hq
  let D := alignedRepair p q m w w'
  let B := sharedSet h u v
  let A := B ∪ D
  have hdis : Disjoint B D := alignedRepair_disjoint p q m h u v ha w w' hw hwU hnwU hmp
  have hsym : ∀ x∈D, -x∈D := alignedRepair_symmetric p q m w w'
  have hinjF : Set.InjOn Prod.fst (D : Set ((ZMod p × ZMod p) × (ZMod q × ZMod q))) :=
    alignedRepair_fst_inj p q m hp2 w w' hw hmp
  have hinjK : Set.InjOn Prod.snd (D : Set ((ZMod p × ZMod p) × (ZMod q × ZMod q))) :=
    alignedRepair_snd_inj p q m hq2 w w' hw' hmq
  have hsF : D.image Prod.fst ⊆ parabolaSet {w,-w} :=
    (alignedRepair_fst_subset p q m w w').trans (repairPoints_subset w (repairInputs p m))
  have hsK : D.image Prod.snd ⊆ parabolaSet {w',-w'} :=
    (alignedRepair_snd_subset p q m w w').trans (repairPoints_subset w' (repairInputs q m))
  have hcard : D.card=2*m := alignedRepair_card p q m hp2 w w' hw hmp
  obtain ⟨horigin,hother⟩ := product_origin_repair h hh u v hF hK ha hb haa hbb hiu hiv
    w w' hw hw' D hdis hsym hinjF hinjK hsF hsK
  change pairCount A A 0=1+D.card at horigin
  rw [hcard] at horigin
  refine ⟨A,fun z ↦ ?_⟩
  by_cases hz : z=0
  · subst z
    rw [horigin]
    have hdiv := Nat.mod_add_div (h^2) 2
    have hmod := Nat.mod_lt (h^2) (by decide : 0<2)
    have he : 1+2*m=h^2 ∨ 1+2*m=h^2+1 := by dsimp [m]; omega
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hpow : (1 : ℝ) ≤ (h : ℝ)^3 := one_le_pow₀ hhR
    rcases he with he | he
    · rw [he]
      push_cast
      nlinarith
    · rw [he]
      push_cast
      nlinarith
  · obtain ⟨hlo,hhi⟩ := hother z hz
    have hroot := sharedRootCount_error_sq h a b hF hK ha hb haa hbb 24 hf hg hfg
      z.1.1 z.1.2 z.2.1 z.2.2
    have hroot' : (sharedRootCount h u v z.1.1 z.1.2 z.2.1 z.2.2-(h : ℝ)^2)^2 ≤ 432*(h : ℝ)^3 := by
      norm_num at hroot
      exact hroot
    have herr := sharedSet_nonzero_error h hh u v ha hb hiu hiv z hz
    have hlo' : (pairCount B B z : ℝ) ≤ pairCount A A z := by exact_mod_cast hlo
    have hhi' : (pairCount A A z : ℝ) ≤ pairCount B B z+8*h+8 := by exact_mod_cast hhi
    exact total_error_sq h (sharedRootCount h u v z.1.1 z.1.2 z.2.1 z.2.2)
      (pairCount B B z) (pairCount A A z) (by exact_mod_cast hh) hroot' herr hlo' hhi'

end Erdos66SharedParameterFlatSet
