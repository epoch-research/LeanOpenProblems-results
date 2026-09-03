import Submission.SharpPrimeBlockVariance
import Submission.PrimeBlockMeanOscillation

/-!
Mean oscillation proportional to reciprocal-prime energy, with no restriction
on individual weights. No Sidon assertion is made.
-/
namespace Erdos1206.SharpPrimeBlockMeanOscillation
open Finset PrimeBlockVariance MovingPrimeBlockVariance SharpPrimeBlockVariance
open PrimeBlockMeanOscillation
open scoped Classical

lemma harmonic_cauchy (P : Finset ℕ) (w : ℕ → ℝ) (_hP : ∀ p ∈ P, 0 < p) :
    (∑ p ∈ P, w p/p)^2 ≤ mass P w*(∑ p ∈ P, (1:ℝ)/p) := by
  have hh := sum_mul_sq_le_sq_mul_sq P
    (fun p => w p/Real.sqrt (p:ℝ)) (fun p => 1/Real.sqrt (p:ℝ))
  have hmul (p : ℕ) : (w p/Real.sqrt (p:ℝ))*(1/Real.sqrt (p:ℝ))=w p/p := by
    rw [div_mul_div_comm,←sq,Real.sq_sqrt (Nat.cast_nonneg p),mul_one]
  have hsq (p : ℕ) : (w p/Real.sqrt (p:ℝ))^2=w p^2/p := by
    rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg p)]
  have hsq' (p : ℕ) : (1/Real.sqrt (p:ℝ))^2=(1:ℝ)/p := by
    rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg p),one_pow]
  simpa only [hmul,hsq,hsq',mass] using hh

lemma mean_difference_sq (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, 0 < p) {U V : ℕ} (hUV : U ≤ V) :
    (mean (P.filter (fun p => p ≤ V)) w-mean (P.filter (fun p => p ≤ U)) w)^2 ≤
      mass P w*((V:ℝ)/(U+1)) := by
  let S := P.filter (fun p => p ≤ U)
  let T := P.filter (fun p => p ≤ V)
  let D := T \ S
  have hST : S ⊆ T := by
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.trans hUV⟩
  have hDP : D ⊆ P := fun p hp => (mem_filter.mp (mem_sdiff.mp hp).1).1
  have hD (p : ℕ) (hp : p ∈ D) : U < p ∧ p ≤ V := by
    obtain ⟨hpT,hpS⟩ := mem_sdiff.mp hp
    have hpU : ¬ p ≤ U := fun hh => hpS (mem_filter.mpr ⟨(mem_filter.mp hpT).1,hh⟩)
    exact ⟨Nat.lt_of_not_ge hpU,(mem_filter.mp hpT).2⟩
  have hcard : D.card ≤ V := by
    have hsub : D ⊆ Icc 1 V := fun p hp => mem_Icc.mpr ⟨hP p (hDP hp),(hD p hp).2⟩
    simpa using card_le_card hsub
  have hharm : (∑ p ∈ D, (1:ℝ)/p) ≤ (V:ℝ)/(U+1) := by
    calc
      _ ≤ ∑ _p ∈ D, (1:ℝ)/(U+1) := by
        apply sum_le_sum
        intro p hp
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (hD p hp).1)
      _ = (D.card:ℝ)/(U+1) := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hmass : mass D w ≤ mass P w :=
    sum_le_sum_of_subset_of_nonneg hDP (fun p _ _ => by positivity)
  change ((∑ p ∈ T, w p/p)-(∑ p ∈ S, w p/p))^2 ≤ _
  rw [←sum_sdiff hST,add_sub_cancel_right]
  calc
    _ ≤ mass D w*(∑ p ∈ D, (1:ℝ)/p) := harmonic_cauchy D w (fun p hp => hP p (hDP hp))
    _ ≤ _ := mul_le_mul hmass hharm (by positivity) (mass_nonneg _ _)

/-- The square of the center oscillation is bounded by 2R times energy. -/
theorem movingMean_oscillation_sq (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) {n m R : ℕ}
    (hn : 0 < n) (hnm : n ≤ m) (hm : m ≤ R*n) (hR : 1 ≤ R) :
    (movingMean P w m-movingMean P w n)^2 ≤ 2*(R:ℝ)*mass P w := by
  have hh := mean_difference_sq P w (fun p hp => (hP p hp).pos) (cutoff_mono hnm)
  change (movingMean P w m-movingMean P w n)^2 ≤
    mass P w*((cutoff m:ℝ)/(cutoff n+1)) at hh
  have hratio : ((cutoff m:ℝ)/(cutoff n+1)) ≤ 2*(R:ℝ) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (cutoff n:ℝ)+1)).mpr
    have hrat : (cutoff m:ℝ) ≤ 2*(R:ℝ)*cutoff n := by exact_mod_cast cutoff_ratio hn hnm hm hR
    nlinarith [show (0:ℝ) ≤ R from Nat.cast_nonneg R]
  have hmul := mul_le_mul_of_nonneg_left hratio (mass_nonneg P w)
  nlinarith

theorem movingMean_oscillation (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) {n m R : ℕ}
    (hn : 0 < n) (hnm : n ≤ m) (hm : m ≤ R*n) (hR : 1 ≤ R) :
    |movingMean P w m-movingMean P w n| ≤ Real.sqrt (2*(R:ℝ)*mass P w) := by
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs,Real.sq_sqrt (mul_nonneg (by positivity) (mass_nonneg _ _))]
  exact movingMean_oscillation_sq P w hP hn hnm hm hR

#print axioms harmonic_cauchy
#print axioms mean_difference_sq
#print axioms movingMean_oscillation
end Erdos1206.SharpPrimeBlockMeanOscillation
