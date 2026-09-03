import Submission.OrdinaryDampedCorrelation
import Submission.FullSmoothL1Obstruction

/-! The fixed-positive-parameter smooth correlation mean is unchanged after
removing every term with a prime input or a prime output. Thus this mean is
not, by itself, a prime-pair lower bound. No settlement of Erdos 972 is claimed. -/
namespace Erdos972CompositeSmoothMean

open Finset Filter
open scoped Topology
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SmoothCorrelationApprox Erdos972FullSmoothL1Obstruction
open Erdos972PrimePowerError Erdos972OrdinaryDampedCorrelation
open Erdos972FixedDampedCorrelation

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def compositeSmoothCorrelation (t α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, if n.Prime ∨ (floorMul α n).Prime then 0
    else smoothMangoldt t n * smoothMangoldt t (floorMul α n)

lemma output_prime_card_le {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    ((Ioc 0 N).filter (fun n => (floorMul α n).Prime)).card ≤
      (floorMul α N).primeCounting := by
  classical
  rw [← prime_card_eq]
  let s := (Ioc 0 N).filter (fun n => (floorMul α n).Prime)
  have hinj : s.card = (s.image (floorMul α)).card :=
    (card_image_of_injective s (floorMul_strictMono hα).injective).symm
  change s.card ≤ _
  rw [hinj]
  apply card_le_card
  intro m hm
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
  obtain ⟨hn, hp⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hn).1,
    (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2⟩, hp⟩

lemma removal_bounds {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) (N : ℕ) :
    0 ≤ smoothCorrelation t α N - compositeSmoothCorrelation t α N ∧
    smoothCorrelation t α N - compositeSmoothCorrelation t α N ≤
      ((N.primeCounting : ℝ) + (floorMul α N).primeCounting) / t^2 := by
  classical
  have hprod (n : ℕ) :
      0 ≤ smoothMangoldt t n * smoothMangoldt t (floorMul α n) ∧
      smoothMangoldt t n * smoothMangoldt t (floorMul α n) ≤ 1/t^2 := by
    refine ⟨mul_nonneg (smoothMangoldt_nonneg ht n) (smoothMangoldt_nonneg ht _), ?_⟩
    simpa only [← div_mul_div_comm, one_mul, ← pow_two, div_pow, one_pow] using
      mul_le_mul (smoothMangoldt_le_inv ht n) (smoothMangoldt_le_inv ht (floorMul α n))
        (smoothMangoldt_nonneg ht (floorMul α n)) (one_div_nonneg.mpr ht.le)
  have hid : smoothCorrelation t α N - compositeSmoothCorrelation t α N =
      ∑ n ∈ Ioc 0 N, if n.Prime ∨ (floorMul α n).Prime
        then smoothMangoldt t n * smoothMangoldt t (floorMul α n) else 0 := by
    simp only [smoothCorrelation, compositeSmoothCorrelation, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    split_ifs <;> simp
  rw [hid]
  constructor
  · apply sum_nonneg
    intro n hn
    split_ifs
    · exact (hprod n).1
    · exact le_rfl
  · calc
      _ ≤ ∑ n ∈ Ioc 0 N,
          ((if n.Prime then 1/t^2 else 0) +
            (if (floorMul α n).Prime then 1/t^2 else 0)) := by
        apply sum_le_sum
        intro n hn
        have h0 : (0 : ℝ) ≤ 1/t^2 := by positivity
        by_cases hp : n.Prime <;> by_cases hq : (floorMul α n).Prime <;>
          simp only [hp, hq, or_self, true_or, false_or, if_true, if_false,
            add_zero, zero_add] <;> linarith only [(hprod n).2, h0]
      _ = (((Ioc 0 N).filter Nat.Prime).card +
          (((Ioc 0 N).filter (fun n => (floorMul α n).Prime)).card : ℝ)) / t^2 := by
        rw [sum_add_distrib, ← sum_filter, ← sum_filter]
        simp only [sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        rw [prime_card_eq]
        exact div_le_div_of_nonneg_right (add_le_add_right
          (Nat.cast_le.mpr (output_prime_card_le hα N)) _) (sq_nonneg t)

lemma output_prime_density_tendsto_zero {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun N : ℕ => ((floorMul α N).primeCounting : ℝ)/(N : ℝ))
      atTop (𝓝 0) := by
  have hM : Tendsto (floorMul α) atTop atTop :=
    tendsto_atTop_mono (self_le_floorMul hα) tendsto_id
  have hh := (primeCounting_div_tendsto_zero.comp hM).const_mul α
  simp only [mul_zero, Function.comp_apply] at hh
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) _ hh
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hMR : (0 : ℝ) < floorMul α N := Nat.cast_pos.mpr (floorMul_pos hα hN)
  have hle : (floorMul α N : ℝ) ≤ α * N := floorMul_le_real hα le_rfl
  have hcount : (0 : ℝ) ≤ (floorMul α N).primeCounting := Nat.cast_nonneg _
  apply (div_le_iff₀ hNR).mpr
  have hh' := mul_le_mul_of_nonneg_left hle (div_nonneg hcount hMR.le)
  convert hh' using 1 <;> field_simp

/-- All terms involving a prime in either coordinate have zero normalized
mass at every fixed positive parameter. This does not concern a parameter
that decreases with N. -/
theorem removed_mean_tendsto_zero {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t) :
    Tendsto (fun N : ℕ =>
      (smoothCorrelation t α N - compositeSmoothCorrelation t α N)/(N : ℝ))
      atTop (𝓝 0) := by
  have hh := (primeCounting_div_tendsto_zero.add
    (output_prime_density_tendsto_zero hα)).div_const (t^2)
  simp only [zero_add, zero_div] at hh
  apply squeeze_zero' (Eventually.of_forall (fun N =>
    div_nonneg (removal_bounds hα ht N).1 (Nat.cast_nonneg N))) _ hh
  filter_upwards with N
  have hb := div_le_div_of_nonneg_right (removal_bounds hα ht N).2
    (Nat.cast_nonneg (α := ℝ) N)
  convert hb using 1
  ring

/-- The full fixed-parameter main term survives deletion of every prime
input and every prime output. In particular this theorem makes no claim
that any prime pair exists. -/
theorem composite_smooth_mean {α t : ℝ} (hα : 1 ≤ α) (hI : Irrational α)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => compositeSmoothCorrelation t α N/(N : ℝ)) atTop
      (𝓝 ((dampedMean t/t)^2)) := by
  have hh := (full_smooth_mean hα hI ht).sub (removed_mean_tendsto_zero hα ht)
  simp only [sub_zero] at hh
  convert hh using 1
  funext N
  ring

#print axioms removal_bounds
#print axioms removed_mean_tendsto_zero
#print axioms composite_smooth_mean

end Erdos972CompositeSmoothMean
