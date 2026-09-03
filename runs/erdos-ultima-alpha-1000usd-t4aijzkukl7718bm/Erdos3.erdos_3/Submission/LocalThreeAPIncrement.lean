import Submission.RelativeStableBohr

/-! Stable local three-term density increments from admissible doubled-center mass.
All supporting windows are selected here; the center-mass condition remains explicit. -/
namespace Erdos3LocalThreeAPIncrement
open Finset Erdos3RelativeStableBohr Erdos3BohrTransport Erdos3DoubledWeights
  Erdos3LocalThreeAPMoment Erdos3LocalSiftedIncrement Erdos3StableSupportedIncrement
  Erdos3BohrIncrementParameters Erdos3FiniteBohr Erdos3BohrCovering Erdos3BohrStableScale
  Erdos3CorrelationMoments Erdos3CorrelationSifting Erdos3BohrLocalAverages
  Erdos3LocalCorrelationCentering Erdos3CrootSisaskL2
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 3500000

def localShrinkDenominator (d z m : ℕ) : ℕ :=
  16*windowDenominator d z*windowDenominator d 1*
    windowDenominator d (stabilityDenominator m (rankBudget m))

lemma localShrinkDenominator_pos (d m : ℕ) {z : ℕ} (hz : 0 < z) :
    0 < localShrinkDenominator d z m := by
  unfold localShrinkDenominator
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (windowDenominator_pos d hz))
    (windowDenominator_pos d (by decide)))
    (windowDenominator_pos d (stabilityDenominator_pos m (rankBudget m)))

lemma nested_window_lower {c u q a b v : ℝ} (ha : 0 < a) (hb : 0 < b) (hv : 0 < v)
    (hu : c/a/4 ≤ u) (hq : u/b/4 ≤ q) : c/(16*a*b*v) ≤ q/v := by
  calc
    _ = (c/a/4/b/4)/v := by ring
    _ ≤ (u/b/4)/v := by gcongr
    _ ≤ _ := div_le_div_of_nonneg_right hq hv.le

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A local three-term-free set with enough admissible center mass has a stable
relative increment, of polynomial relative rank and explicit radius loss. -/
theorem local_threeAP_increment (h2 : Function.Bijective (fun x : G ↦ x+x))
    (E : Finset (AddChar G ℂ)) {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    {z : ℕ} (hz : 0 < z) (hbase : RelativeStable E z r) (houter : RelativeStable E z c)
    (hcr : 4*c ≤ relativeWidth E z r)
    (A Z : Finset G) (hA : A.Nonempty) (hAB : A ⊆ bohr E r) (hZA : Z ⊆ A)
    (hfree : ThreeAPFree (A : Set G))
    (hsize : 8 ≤ (relativeDensity A (bohr E r))^2*((bohr E r).card : ℝ))
    (hcenters : ∀ a ∈ Z, a+a ∈ bohr E (relativeWidth E z r))
    {p m : ℕ} (hp : 67 ≤ p) (hpeven : Even p) (hm : 0 < m)
    (hmass : (2/3 : ℝ)^p ≤ doubledMass Z
      (corr (normalized (bohr (transportChars (doublingEquiv G h2) E) c))))
    (hcenterError : (1/(z : ℝ))*(2/relativeDensity A (bohr E r)+1) ≤ 1/256)
    (hlocalError : (1/(z : ℝ))*(1/relativeDensity A (bohr E r))^(8*p) ≤
      (17/16 : ℝ)^(8*p)-(67/64 : ℝ)^(8*p))
    (hbudget : 4 ≤ (2 : ℝ)^(2*m)*(relativeDensity A (bohr E r))^(2*(8*p))) :
    ∃ F : Finset (AddChar G ℂ), F.card ≤ E.card+rankBudget m ∧ ∃ s : ℝ,
      min (c/(localShrinkDenominator E.card z m : ℝ))
        (generatorRadius m (rankBudget m))/2 ≤ s ∧
      0 < s ∧ s ≤ c ∧ RelativeStable F z s ∧
      ∃ x : G, (129/128 : ℝ)*relativeDensity A (bohr E r) ≤ smooth (bohr F s) (indicator A) x := by
  let E' := transportChars (doublingEquiv G h2) E
  have hEcard : E'.card = E.card := transportChars_card _ _
  have hα := relativeDensity_pos A (bohr E r) hA hAB
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hδ : (0 : ℝ) < 1/z := one_div_pos.mpr hzR
  have hδsmall : (1/(z : ℝ)) ≤ 1/256 := by
    have hp : (0 : ℝ) ≤ (1/(z : ℝ))*(2/relativeDensity A (bohr E r)) := by positivity
    nlinarith
  have hbasewidth := relativeWidth_pos E hz hr
  have hCwidth := relativeWidth_pos E' hz hc
  have houter' : RelativeStable E' z c := houter.transport (doublingEquiv G h2)
  have hCne : (bohr E' c).Nonempty := ⟨0,bohr_zero _ hc.le⟩
  have hmoment : (17/16 : ℝ)^(8*p) ≤ 𝔼 t : G, corr (normalized (bohr E' c)) t*
      (corr (localNormalized A (bohr E r)) t/density (bohr E r))^(8*p) := by
    apply local_threeAP_weighted_gain E hr.le hbasewidth.le hδ.le hbase A Z hA hAB hZA
      hfree hsize hcenterError (normalized (bohr E' c)) (normalized_nonneg _)
      (expect_normalized _ hCne) (normalized_even _ (fun x hx ↦ bohr_neg hx))
    · intro t ht
      have hs : corr (normalized ((bohr E c).image (doublingEquiv G h2))) t ≠ 0 := by
        simpa only [transport_bohr] using ht
      exact bohr_mono E hcr (doubled_weight_support h2 E (bohr E c) (subset_refl _) hs)
    · exact hcenters
    · omega
    · exact hpeven
    · exact hmass
  obtain ⟨u,huLo,huHi,huStable⟩ := exists_relative_stable E' (by positivity : 0 < relativeWidth E' z c/4)
    (z := 1) (by decide)
  have hu : 0 < u := by linarith
  have huC : u ≤ relativeWidth E' z c := by linarith
  have hUwidth := relativeWidth_pos E' (z := 1) (by decide) hu
  let zQ := stabilityDenominator m (rankBudget m)
  have hzQ : 0 < zQ := stabilityDenominator_pos m (rankBudget m)
  obtain ⟨q,hqLo,hqHi,hqStable⟩ := exists_relative_stable E'
    (by positivity : 0 < relativeWidth E' 1 u/4) hzQ
  have hq : 0 < q := by linarith
  have hqU : q ≤ relativeWidth E' 1 u := by linarith
  have hQwidth := relativeWidth_pos E' hzQ hq
  have hUgrowth : ((bohr E' (u+q)).card : ℝ) ≤ 2*((bohr E' u).card : ℝ) := by
    simpa only [Nat.cast_one, div_one, show (1 : ℝ)+1 = 2 by norm_num]
      using huStable.enlargement (by decide : 0 < (1 : ℕ)) hqU hu.le
  let V := bohr E (r+2*c)
  have hV : V.Nonempty := ⟨0,bohr_zero E (by positivity)⟩
  have hsupport : ∀ a ∈ A, ∀ t ∈ bohr E' c, a-t ∈ V := by
    intro a ha t ht
    simpa only [sub_eq_add_neg, V] using bohr_add (hAB ha) (bohr_neg (doubled_bohr_subset h2 E c ht))
  have hVsize : density V ≤ (67/64 : ℝ)*density (bohr E r) := by
    have hh := hbase.enlargement hz (by linarith : 2*c ≤ relativeWidth E z r) hr.le
    have hb : ((bohr E (r+2*c)).card : ℝ) ≤ (67/64 : ℝ)*((bohr E r).card : ℝ) :=
      hh.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
    unfold density V
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
  have hQgrowth : ((bohr E' (q+relativeWidth E' zQ q)).card : ℝ) ≤
      (1+translationTolerance m (rankBudget m))*((bohr E' (q-relativeWidth E' zQ q)).card : ℝ) := hqStable
  obtain ⟨D,hD,s,hsLo,hsHi,hsGrowth,x,hx⟩ := moment_to_stable_increment E' hc.le hCwidth.le
    hδ.le (by linarith) hu.le huC hq.le hQwidth houter' hUgrowth A (bohr E r) V hA hAB hV
    hsupport hVsize (p := 8*p) (by omega) hm hmoment hlocalError hbudget hQgrowth hz
  let w := min (relativeWidth E' zQ q) (generatorRadius m (rankBudget m))
  have hw : 0 < w := lt_min hQwidth (generatorRadius_pos m (rankBudget m))
  have hw' := stabilityWidth_pos (E' ∪ D) hz (by positivity : 0 < w/2)
  have hs : 0 < s := by linarith
  have hsU : s ≤ w := by linarith
  have hqLower : c/(localShrinkDenominator E.card z m : ℝ) ≤ relativeWidth E' zQ q := by
    have hh := nested_window_lower
      (by exact_mod_cast windowDenominator_pos E'.card hz : (0 : ℝ) < windowDenominator E'.card z)
      (by exact_mod_cast windowDenominator_pos E'.card (by decide : 0 < (1 : ℕ)) : (0 : ℝ) < windowDenominator E'.card 1)
      (by exact_mod_cast windowDenominator_pos E'.card hzQ : (0 : ℝ) < windowDenominator E'.card zQ)
      huLo hqLo
    simpa only [relativeWidth, localShrinkDenominator, Nat.cast_mul, Nat.cast_ofNat, hEcard, zQ] using hh
  have hsLower : min (c/(localShrinkDenominator E.card z m : ℝ))
      (generatorRadius m (rankBudget m))/2 ≤ s := by
    have hmin := min_le_min_right (generatorRadius m (rankBudget m)) hqLower
    linarith
  have hsC : s ≤ c := by
    have hqle := relativeWidth_le_quarter E' hzQ hq.le
    have hule := relativeWidth_le_quarter E' (z := 1) (by decide) hu.le
    have hcle := relativeWidth_le_quarter E' hz hc.le
    have hsw : s ≤ relativeWidth E' zQ q := hsU.trans (min_le_left _ _)
    linarith
  have hstable : RelativeStable (E' ∪ D) z s :=
    stable_growth_mono _ (relativeWidth_le_stabilityWidth _ z (by linarith : s ≤ 2*(w/2)))
      hδ.le le_rfl hsGrowth
  refine ⟨E' ∪ D,?_,s,hsLower,hs,hsC,hstable,x,hx⟩
  exact (card_union_le _ _).trans (by omega)

#print axioms local_threeAP_increment
end Erdos3LocalThreeAPIncrement
