import Submission.GlobalTwoScaleMean
import Submission.DampedMeanMonotonic

/-! Every fixed positive parameter gives an eventually negative
smooth-weighted sum of the new global minorant. No conclusion is drawn
about its moving-parameter or prime-weighted sums. -/
namespace Erdos972GlobalTwoScaleAllParameters

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972GlobalTwoScaleMinorant Erdos972GlobalTwoScaleMean
open Erdos972DampedMeanMonotonic Erdos972FixedDampedCorrelation
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972FullSmoothL1Obstruction Erdos972PrimePowerError
open Erdos972SignedSmoothMinorant Erdos972TwoScalePairMinorant

set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma mixedDampedLowerMean_neg {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    mixedDampedLowerMean s t < 0 := by
  have hB := dampedMean_strictMono ht (show t < 2*t by linarith)
  have hdiff : dampedMean t/t/2-dampedMean (2*t)/(2*t) < 0 := by
    have he : dampedMean t/t/2-dampedMean (2*t)/(2*t) =
        (dampedMean t-dampedMean (2*t))/(2*t) := by ring
    rw [he]
    exact div_neg_of_neg_of_pos (sub_neg.mpr hB) (by positivity)
  exact mul_neg_of_pos_of_neg (div_pos (dampedMean_pos hs) hs) hdiff

/-- Compatibility name for the current, unit-corrected global minorant. -/
noncomputable def globalLower (t : ℝ) (n : ℕ) : ℝ := globalMinorant t n

lemma globalLower_le {t : ℝ} (ht : 0 < t) (n : ℕ) : globalLower t n ≤ Λ n :=
  globalMinorant_le_mangoldt ht n

lemma globalLower_le_smooth {t : ℝ} (ht : 0 < t) (n : ℕ) :
    globalLower t n ≤ smoothMangoldt t n := by
  by_cases hn : IsPrimePow n
  · exact primePower_le ht hn
  · exact (nonPrimePower_nonpos ht hn).trans (smoothMangoldt_nonneg ht n)

/-- Undamping can increase this signed lower weight only by its overlap
with the actual Mangoldt function. The overlap has zero fixed-parameter mean. -/
lemma globalLower_le_damped_add_overlap {t : ℝ} (ht : 0 < t) (n : ℕ) :
    globalLower t n ≤ dampedLower t n+min (smoothMangoldt t n) (Λ n) := by
  have hx0 := (halfDamping_pos t n).le
  have hx1 := halfDamping_le_one ht.le n
  have hmin : globalLower t n ≤ min (smoothMangoldt t n) (Λ n) :=
    le_min (globalLower_le_smooth ht n) (globalLower_le ht n)
  have hmin0 : 0 ≤ min (smoothMangoldt t n) (Λ n) :=
    le_min (smoothMangoldt_nonneg ht n) vonMangoldt_nonneg
  have h₁ := mul_le_mul_of_nonneg_left hmin (sub_nonneg.mpr hx1)
  have h₂ := mul_nonneg hx0 hmin0
  have he : halfDamping t n*globalLower t n = dampedLower t n := by
    exact (dampedLower_eq_halfDamping_mul ht n).symm
  nlinarith only [h₁, h₂, he]

noncomputable def outputOverlap (t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, min (smoothMangoldt t (floorMul α n)) (Λ (floorMul α n))

lemma outputOverlap_nonneg {t : ℝ} (ht : 0 < t) (α : ℝ) (N : ℕ) :
    0 ≤ outputOverlap t α N :=
  sum_nonneg (fun _ _ => le_min (smoothMangoldt_nonneg ht _) vonMangoldt_nonneg)

lemma outputOverlap_bound {t α : ℝ} (ht : 0 < t) (hα : 1 ≤ α) (N : ℕ) :
    outputOverlap t α N ≤ smoothOverlap t (floorMul α N) := by
  unfold outputOverlap smoothOverlap
  calc
    _ = ∑ m ∈ (Ioc 0 N).image (floorMul α), min (smoothMangoldt t m) (Λ m) := by
      rw [sum_image]
      exact fun n hn m hm he => (floorMul_strictMono hα).injective he
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        exact mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hn).1,
          (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2⟩
      · intro m hm hnot
        exact le_min (smoothMangoldt_nonneg ht m) vonMangoldt_nonneg

lemma outputOverlap_mean_zero {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) :
    Tendsto (fun N : ℕ => outputOverlap t α N/(N:ℝ)) atTop (𝓝 0) := by
  have hg : Tendsto (floorMul α) atTop atTop :=
    tendsto_atTop_mono (self_le_floorMul hα) tendsto_id
  have hh := ((smoothOverlap_mean_tendsto_zero ht).comp hg).const_mul α
  simp only [mul_zero] at hh
  apply squeeze_zero' (Eventually.of_forall (fun N =>
    div_nonneg (outputOverlap_nonneg ht α N) (Nat.cast_nonneg N))) _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hMR : (0:ℝ) < floorMul α N := Nat.cast_pos.mpr (floorMul_pos hα hN)
  have hle : (floorMul α N:ℝ) ≤ α*N := floorMul_le_real hα le_rfl
  have hpos := smoothOverlap_nonneg ht (floorMul α N)
  apply (div_le_div_of_nonneg_right (outputOverlap_bound ht hα N) hNR.le).trans
  apply (div_le_iff₀ hNR).mpr
  have hb := mul_le_mul_of_nonneg_left hle (div_nonneg hpos hMR.le)
  have he : (smoothOverlap t (floorMul α N)/(floorMul α N:ℝ))*(floorMul α N:ℝ) =
      smoothOverlap t (floorMul α N) := div_mul_cancel₀ _ hMR.ne'
  dsimp only [Function.comp_apply]
  nlinarith only [hb, he]

noncomputable def mixedGlobalLower (s t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, smoothMangoldt s n*globalLower t (floorMul α n)

lemma mixedGlobalLower_upper {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (α : ℝ) (N : ℕ) :
    mixedGlobalLower s t α N ≤ mixedDampedLower s t α N+outputOverlap t α N/s := by
  unfold mixedGlobalLower mixedDampedLower outputOverlap
  rw [sum_div, ← sum_add_distrib]
  apply sum_le_sum
  intro n hn
  have h₁ := mul_le_mul_of_nonneg_left
    (globalLower_le_damped_add_overlap ht (floorMul α n)) (smoothMangoldt_nonneg hs n)
  have h₂ := mul_le_mul_of_nonneg_right (smoothMangoldt_le_inv hs n)
    (le_min (smoothMangoldt_nonneg ht (floorMul α n)) (vonMangoldt_nonneg (n := floorMul α n)))
  calc
    _ ≤ smoothMangoldt s n*dampedLower t (floorMul α n)+
        smoothMangoldt s n*min (smoothMangoldt t (floorMul α n)) (Λ (floorMul α n)) := by
      nlinarith only [h₁]
    _ ≤ _ := by
      simpa only [one_div_mul_eq_div, add_comm] using add_le_add_left h₂
        (smoothMangoldt s n*dampedLower t (floorMul α n))

/-- The actual undamped global minorant is eventually negative on smooth
inputs for EVERY pair of fixed positive parameters. This does not assert
any estimate at moving parameters or with a genuine prime source weight. -/
theorem eventually_mixedGlobalLower_negative {α s t : ℝ} (hα : 1 ≤ α) (hI : Irrational α)
    (hs : 0 < s) (ht : 0 < t) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, mixedGlobalLower s t α N < -c*(N:ℝ) := by
  let c := -(mixedDampedLowerMean s t)/2
  have hm := mixedDampedLowerMean_neg hs ht
  have hc : 0 < c := by dsimp [c]; linarith only [hm]
  have hlim := (mixedDampedLower_fixed_mean hα hI hs ht).add
    ((outputOverlap_mean_zero hα ht).div_const s)
  simp only [zero_div, add_zero] at hlim
  have hb := (tendsto_order.mp hlim).2 (-c)
    (show mixedDampedLowerMean s t < -c by dsimp [c]; linarith only [hm])
  refine ⟨c, hc, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1:ℕ)] with N hN hNpos
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hNpos
  have hu := div_le_div_of_nonneg_right (mixedGlobalLower_upper hs ht α N) hNR.le
  have he : (mixedDampedLower s t α N+outputOverlap t α N/s)/(N:ℝ) =
      mixedDampedLower s t α N/(N:ℝ)+(outputOverlap t α N/(N:ℝ))/s := by ring
  rw [he] at hu
  exact (div_lt_iff₀ hNR).mp (hu.trans_lt hN)

#print axioms mixedDampedLowerMean_neg
#print axioms globalLower_le_damped_add_overlap
#print axioms outputOverlap_mean_zero
#print axioms eventually_mixedGlobalLower_negative

end Erdos972GlobalTwoScaleAllParameters
