import Submission.LocalThreeAPIncrement
import Submission.SimultaneousWindows

/-! Elimination of the admissible-center hypothesis: a local three-term-free set
has a density increment unless its current Bohr base is small. -/
namespace Erdos3LocalDensityStep
open Finset Erdos3LocalThreeAPIncrement Erdos3RelativeStableBohr Erdos3SimultaneousWindows
  Erdos3BohrTransport Erdos3DoubledWeights Erdos3LocalThreeAPMoment Erdos3AsymmetricSifting
  Erdos3StableSupportedIncrement Erdos3BohrIncrementParameters Erdos3FiniteBohr
  Erdos3BohrCovering Erdos3CorrelationMoments Erdos3CorrelationSifting
  Erdos3BohrLocalAverages Erdos3LocalCorrelationCentering Erdos3CrootSisaskL2
  Erdos3PopularAlmostPeriods
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4000000

def coverFactor (d z : ℕ) : ℕ := (16*windowDenominator d z+1)^(2*d)
def stepShrinkDenominator (d z m : ℕ) : ℕ :=
  64*(windowDenominator d z)^2*localShrinkDenominator d z m

lemma coverFactor_pos (d z : ℕ) : 0 < coverFactor d z := by unfold coverFactor; positivity
lemma stepShrinkDenominator_pos (d m : ℕ) {z : ℕ} (hz : 0 < z) :
    0 < stepShrinkDenominator d z m := by
  unfold stepShrinkDenominator
  exact Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos (windowDenominator_pos d hz) _))
    (localShrinkDenominator_pos d m hz)

lemma retained_lower {a α β δ : ℝ} (ha : a ≤ α) (hδ : δ ≤ a/2048)
    (hβ : (1-1/1024 : ℝ)*α-2*δ ≤ β) : (511/512 : ℝ)*α ≤ β := by linarith

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma smooth_window_le (A U V : Finset G) (x y : G) :
    smooth V (indicator (window A U x)) y ≤ smooth V (indicator A) (x+y) := by
  apply expect_le_expect
  intro v _
  change indicator (window A U x) (y+(v : G)) ≤ indicator A (x+y+(v : G))
  by_cases hm : y+(v : G) ∈ window A U x
  · have hh := (mem_filter.mp hm).2
    simp only [indicator, if_pos hm, add_assoc, if_pos hh, le_refl]
  · simp only [indicator, if_neg hm]
    split_ifs <;> norm_num

lemma exists_smooth_ge_diffSmooth (C : Finset G) (hC : C.Nonempty) (f : G → ℝ) (x : G) :
    ∃ y : G, diffSmooth C f x ≤ smooth C f y := by
  letI : Nonempty C := hC.to_subtype
  obtain ⟨y,_,hy⟩ := exists_max_image (univ : Finset G) (smooth C f) univ_nonempty
  refine ⟨y,?_⟩
  have he : diffSmooth C f x = 𝔼 c : C, smooth C f (x-(c : G)) := by
    unfold diffSmooth smooth
    apply expect_congr rfl
    intro c _
    apply expect_congr rfl
    intro d _
    congr 1
    abel
  rw [he]
  exact expect_le univ_nonempty (fun c _ ↦ hy _ (mem_univ _))

lemma nonempty_of_relative_pos (A B : Finset G) (h : 0 < relativeDensity A B) : A.Nonempty := by
  by_contra hn
  have he : A = ∅ := not_nonempty_iff_eq_empty.mp hn
  simp [he,relativeDensity] at h

/-- The center-mass assumption is removed. All numerical parameters may be fixed
in advance from a lower bound a for the current relative density. -/
theorem local_density_step (h2 : Function.Bijective (fun x : G ↦ x+x))
    (E : Finset (AddChar G ℂ)) {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    {z p m : ℕ} (hz : 0 < z) (hp : 67 ≤ p) (hpeven : Even p) (hm : 0 < m)
    (hstable : RelativeStable E z r)
    (A : Finset G) (hA : A.Nonempty) (hAB : A ⊆ bohr E r)
    (hfree : ThreeAPFree (A : Set G)) (haA : a ≤ relativeDensity A (bohr E r))
    (hmeanError : 1/(z : ℝ) ≤ a/2048)
    (hmassParam : (2/3 : ℝ)^p ≤ a/2)
    (hcenterError : (1/(z : ℝ))*(4/a+1) ≤ 1/256)
    (hlocalError : (1/(z : ℝ))*(2/a)^(8*p) ≤ (17/16 : ℝ)^(8*p)-(67/64 : ℝ)^(8*p))
    (hbudget : 4 ≤ (2 : ℝ)^(2*m)*(a/2)^(2*(8*p)))
    (hlarge : 32*(coverFactor E.card z : ℝ) ≤ a^2*((bohr E r).card : ℝ)) :
    ∃ F : Finset (AddChar G ℂ), F.card ≤ E.card+rankBudget m ∧ ∃ s : ℝ,
      min (r/(stepShrinkDenominator E.card z m : ℝ))
        (generatorRadius m (rankBudget m))/2 ≤ s ∧
      0 < s ∧ s ≤ r ∧ RelativeStable F z s ∧
      ∃ x : G, (1025/1024 : ℝ)*relativeDensity A (bohr E r) ≤ smooth (bohr F s) (indicator A) x := by
  let α := relativeDensity A (bohr E r)
  have hα : 0 < α := relativeDensity_pos A (bohr E r) hA hAB
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hBwidth := relativeWidth_pos E hz hr
  obtain ⟨w,hwLo,hwHi,hwStable⟩ := exists_relative_stable E
    (by positivity : 0 < relativeWidth E z r/4) hz
  have hw : 0 < w := by linarith
  have hwB : w ≤ relativeWidth E z r := by linarith
  have hWwidth := relativeWidth_pos E hz hw
  obtain ⟨c,hcLo,hcHi,hcStable⟩ := exists_relative_stable E
    (by positivity : 0 < relativeWidth E z w/16) hz
  have hc : 0 < c := by linarith
  have hcW : c ≤ w := by
    have hh := relativeWidth_le_quarter E hz hw.le
    linarith
  have hwR : w ≤ r := by
    have hh := relativeWidth_le_quarter E hz hr.le
    linarith
  have hcLower : r/(64*(windowDenominator E.card z : ℝ)^2) ≤ c := by
    calc
      _ = (relativeWidth E z r/4)/(windowDenominator E.card z : ℝ)/16 := by
        unfold relativeWidth
        ring
      _ ≤ w/(windowDenominator E.card z : ℝ)/16 := by gcongr
      _ ≤ c := hcLo
  have hLD : (0 : ℝ) < localShrinkDenominator E.card z m := by
    exact_mod_cast localShrinkDenominator_pos E.card m hz
  have hLD1 : (1 : ℝ) ≤ localShrinkDenominator E.card z m := by
    exact_mod_cast localShrinkDenominator_pos E.card m hz
  have hstepLower : r/(stepShrinkDenominator E.card z m : ℝ) ≤
      c/(localShrinkDenominator E.card z m : ℝ) := by
    have hh := div_le_div_of_nonneg_right hcLower hLD.le
    simpa only [stepShrinkDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_div] using hh
  have hcommon : min (r/(stepShrinkDenominator E.card z m : ℝ))
      (generatorRadius m (rankBudget m))/2 ≤ c := by
    have hh := (min_le_left (r/(stepShrinkDenominator E.card z m : ℝ))
      (generatorRadius m (rankBudget m))).trans hstepLower
    have hh' : c/(localShrinkDenominator E.card z m : ℝ) ≤ c := div_le_self hc.le hLD1
    linarith
  have hWne : (bohr E w).Nonempty := ⟨0,bohr_zero _ hw.le⟩
  have hCne : (bohr E c).Nonempty := ⟨0,bohr_zero _ hc.le⟩
  by_cases hWupper : ∀ x ∈ bohr E r, smooth (bohr E w) (indicator A) x ≤ (1+1/1024 : ℝ)*α
  · by_cases hCupper : ∀ x ∈ bohr E r, diffSmooth (bohr E c) (indicator A) x ≤ (1+1/1024 : ℝ)*α
    · let U := bohr E (relativeWidth E z w/2)
      have hUW : U ⊆ bohr E w := bohr_mono E (by
        have hh := relativeWidth_le_quarter E hz hw.le
        linarith : relativeWidth E z w/2 ≤ w)
      have hCsub : ∀ b ∈ bohr E c, ∀ d ∈ bohr E c, d-b ∈ U := by
        intro b hb d hd
        have hh := bohr_add hd (bohr_neg hb)
        apply bohr_mono E (by linarith : c+c ≤ relativeWidth E z w/2)
        simpa only [sub_eq_add_neg] using hh
      obtain ⟨x,hx,hZA,hwin,hmass⟩ := exists_simultaneous_windows h2 E hr.le hBwidth.le
        (by positivity : (0 : ℝ) ≤ 1/z) hstable A (bohr E w) U (bohr E c)
        hWne hCne hUW (bohr_mono E hwB) hCsub hWupper hCupper
      let A' := window A (bohr E w) x
      let Z := window A U x
      have hret : (511/512 : ℝ)*α ≤ relativeDensity A' (bohr E w) :=
        retained_lower haA hmeanError hwin
      have hretMass : (511/512 : ℝ)*α ≤ doubledMass Z
          (corr (normalized ((bohr E c).image (doublingEquiv G h2)))) :=
        retained_lower haA hmeanError hmass
      have hα' : 0 < relativeDensity A' (bohr E w) := lt_of_lt_of_le (by positivity) hret
      have hA' := nonempty_of_relative_pos A' (bohr E w) hα'
      have hA'B : A' ⊆ bohr E w := window_subset ..
      have ha' : a/2 ≤ relativeDensity A' (bohr E w) := by linarith
      have hfree' : ThreeAPFree (A' : Set G) := window_threeAPFree A (bohr E w) hfree x
      have hsize' : 8 ≤ (relativeDensity A' (bohr E w))^2*((bohr E w).card : ℝ) := by
        have hcard : ((bohr E r).card : ℝ) ≤ (coverFactor E.card z : ℝ)*((bohr E w).card : ℝ) := by
          exact_mod_cast initial_window_card_bound E hz hr hwLo
        have hcf : (0 : ℝ) < coverFactor E.card z := by exact_mod_cast coverFactor_pos E.card z
        have hh := mul_le_mul_of_nonneg_left hcard (sq_nonneg a)
        have hnum : (32 : ℝ) ≤ a^2*((bohr E w).card : ℝ) := by
          apply (mul_le_mul_iff_left₀ hcf).mp
          nlinarith [hlarge.trans hh]
        have hsquare : (a/2)^2 ≤ (relativeDensity A' (bohr E w))^2 :=
          pow_le_pow_left₀ (by positivity) ha' 2
        have hmul := mul_le_mul_of_nonneg_right hsquare (Nat.cast_nonneg (bohr E w).card)
        nlinarith
      have hcenter' : ∀ a ∈ Z, a+a ∈ bohr E (relativeWidth E z w) := by
        intro a haZ
        have hh := bohr_add (window_subset A U x haZ) (window_subset A U x haZ)
        simpa only [U, add_halves] using hh
      have hmass' : (2/3 : ℝ)^p ≤ doubledMass Z
          (corr (normalized (bohr (transportChars (doublingEquiv G h2) E) c))) := by
        rw [← transport_bohr]
        linarith
      have hcentErr : (1/(z : ℝ))*(2/relativeDensity A' (bohr E w)+1) ≤ 1/256 := by
        have hh : 2/relativeDensity A' (bohr E w) ≤ 4/a := by
          apply (div_le_div_iff₀ hα' ha).mpr
          linarith
        have hs : 2/relativeDensity A' (bohr E w)+1 ≤ 4/a+1 := by linarith
        exact (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 1/z)).trans hcenterError
      have hlocErr : (1/(z : ℝ))*(1/relativeDensity A' (bohr E w))^(8*p) ≤
          (17/16 : ℝ)^(8*p)-(67/64 : ℝ)^(8*p) := by
        have hh : 1/relativeDensity A' (bohr E w) ≤ 2/a := by
          apply (div_le_div_iff₀ hα' ha).mpr
          linarith
        exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh _) (by positivity)).trans hlocalError
      have hbudget' : 4 ≤ (2 : ℝ)^(2*m)*(relativeDensity A' (bohr E w))^(2*(8*p)) :=
        hbudget.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha' _) (by positivity))
      obtain ⟨F,hF,s,hsLo,hs,hsC,hsStable,y,hy⟩ := local_threeAP_increment h2 E hw hc hz hwStable hcStable
        (by linarith) A' Z hA' hA'B hZA hfree' hsize' hcenter' hp hpeven hm hmass' hcentErr hlocErr hbudget'
      refine ⟨F,hF,s,?_,hs,hsC.trans (hcW.trans hwR),hsStable,x+y,?_⟩
      · have hh := min_le_min_right (generatorRadius m (rankBudget m)) hstepLower
        linarith
      · have hgain : (1025/1024 : ℝ)*α ≤ (129/128 : ℝ)*relativeDensity A' (bohr E w) := by
          nlinarith
        exact (hgain.trans hy).trans (smooth_window_le A (bohr E w) (bohr F s) x y)
    · push_neg at hCupper
      obtain ⟨x,hx,hbig⟩ := hCupper
      obtain ⟨y,hy⟩ := exists_smooth_ge_diffSmooth (bohr E c) hCne (indicator A) x
      refine ⟨E,by omega,c,hcommon,hc,hcW.trans hwR,hcStable,y,?_⟩
      change (1025/1024 : ℝ)*α ≤ smooth (bohr E c) (indicator A) y
      linarith
  · push_neg at hWupper
    obtain ⟨x,hx,hbig⟩ := hWupper
    refine ⟨E,by omega,w,hcommon.trans hcW,hw,hwR,hwStable,x,?_⟩
    change (1025/1024 : ℝ)*α ≤ smooth (bohr E w) (indicator A) x
    linarith

#print axioms local_density_step
end Erdos3LocalDensityStep
