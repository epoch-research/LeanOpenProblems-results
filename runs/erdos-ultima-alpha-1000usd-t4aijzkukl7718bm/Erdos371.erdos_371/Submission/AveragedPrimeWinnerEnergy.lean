import Submission.PrimeWinnerEnergyIncrement

/-! A Cesàro energy criterion for Erdős 371. It is enough to bound the sum
of prime-winner energies through X by O(X²), rather than bound each energy
by O(X). The required arithmetic bound is not asserted here. -/

namespace Erdos371
open Finset Filter
open scoped Topology

/-- A large prefix sum of a unit-bounded sequence persists over sufficiently
many nearby endpoints to force a cubic lower bound on their square energy. -/
lemma unit_prefix_cube_le_square_sum (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (N : ℕ) :
    |∑ n ∈ range N, f n|^3 ≤
      8 * ∑ k ∈ range (2*N+1), (∑ n ∈ range k, f n)^2 := by
  let A (k : ℕ) : ℝ := ∑ n ∈ range k, f n
  let a : ℝ := |A N|
  let m : ℕ := ⌊a/2⌋₊
  have ha : 0 ≤ a := abs_nonneg _
  have hAN : a ≤ N := by
    exact (abs_sum_le_sum_abs _ _).trans (by
      simpa using (sum_le_sum (fun n (_ : n ∈ range N) => hf n)))
  have hm : (m : ℝ) ≤ a/2 := Nat.floor_le (by positivity)
  have hm' : a/2 ≤ (m : ℝ)+1 := (Nat.lt_floor_add_one (a/2)).le
  have hmN : m ≤ N := by
    have : (m : ℝ) ≤ N := by linarith
    exact_mod_cast this
  let T := Icc N (N+m)
  have hT : T ⊆ range (2*N+1) := by
    intro k hk
    obtain ⟨_,hk⟩ := mem_Icc.mp hk
    exact mem_range.mpr (by omega)
  have hstep (k : ℕ) (hk : k ∈ T) : a/2 ≤ |A k| := by
    obtain ⟨hNk,hkN⟩ := mem_Icc.mp hk
    have hdiff : |A k-A N| ≤ (k-N : ℕ) := by
      dsimp [A]
      rw [← sum_range_add_sum_Ico f hNk,add_sub_cancel_left]
      exact (abs_sum_le_sum_abs _ _).trans (by
        simpa using (sum_le_sum (fun n (_ : n ∈ Ico N k) => hf n)))
    have hkm : (k-N : ℕ) ≤ m := by omega
    have hkmr : ((k-N : ℕ) : ℝ) ≤ m := by exact_mod_cast hkm
    have ht := abs_sub_le (A N) (A k) 0
    simp only [sub_zero] at ht
    rw [abs_sub_comm (A N) (A k)] at ht
    dsimp [a] at hm ⊢
    linarith
  have hsq (k : ℕ) (hk : k ∈ T) : a^2/4 ≤ (A k)^2 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ a/2) (hstep k hk) 2
    rw [sq_abs] at h
    nlinarith
  have hsum := sum_le_sum hsq
  have hcard : T.card = m+1 := by simp only [T,Nat.card_Icc]; omega
  simp only [sum_const,nsmul_eq_mul,hcard,Nat.cast_add,Nat.cast_one] at hsum
  have hsub : (∑ k ∈ T, (A k)^2) ≤ ∑ k ∈ range (2*N+1), (A k)^2 :=
    sum_le_sum_of_subset_of_nonneg hT (by intros; positivity)
  have hprod := mul_le_mul_of_nonneg_right hm' (sq_nonneg a)
  change a^3 ≤ 8 * ∑ k ∈ range (2*N+1), (A k)^2
  nlinarith

noncomputable def cumulativePrimeWinnerEnergy (X : ℕ) : ℝ :=
  ∑ k ∈ range (X+1), primeWinnerEnergy k

lemma cumulativePrimeWinnerEnergy_nonneg (X : ℕ) :
    0 ≤ cumulativePrimeWinnerEnergy X := by
  unfold cumulativePrimeWinnerEnergy primeWinnerEnergy
  positivity

/-- A finite persistence bound. No arithmetic cancellation is assumed. -/
theorem comparison_cube_le_cumulative_primeWinnerEnergy (N : ℕ) :
    |(risingCount N : ℝ)-fallingCount N|^3 ≤
      8 * (primeWinnerLabels (2*N)).card * cumulativePrimeWinnerEnergy (2*N) := by
  have h := unit_prefix_cube_le_square_sum factorSign
    (fun n => by simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))) N
  simp_rw [factorSign_sum_eq_signed_count] at h
  have hrow (k : ℕ) (hk : k ∈ range (2*N+1)) :
      ((risingCount k : ℝ)-fallingCount k)^2 ≤
        (primeWinnerLabels (2*N)).card * primeWinnerEnergy k := by
    have hcard := card_le_card (primeWinnerLabels_mono (show k ≤ 2*N by
      have := mem_range.mp hk; omega))
    exact (comparison_sq_le_primeWinnerEnergy k).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (by unfold primeWinnerEnergy; positivity))
  have hs := sum_le_sum hrow
  rw [← mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 8)
  exact h.trans (by simpa only [cumulativePrimeWinnerEnergy,mul_assoc] using ht)

lemma doubled_primeWinnerLabels_card_ratio_zero :
    Tendsto (fun N : ℕ => ((primeWinnerLabels (2*N)).card : ℝ)/N) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have h := (primeWinnerLabels_card_tendsto_zero.comp hN).const_mul 2
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  simp only [Function.comp_apply,Nat.cast_mul,Nat.cast_ofNat]
  field_simp

/-- A quadratic bound on cumulative energy suffices. This permits energy
spikes that a pointwise linear bound would exclude. The hypothesis is a
substantive unproved arithmetic estimate. -/
theorem density_of_quadratic_cumulative_primeWinnerEnergy (C : ℝ)
    (hE : ∀ᶠ X : ℕ in atTop, cumulativePrimeWinnerEnergy X ≤ C*(X : ℝ)^2) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  have hN : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have ht := doubled_primeWinnerLabels_card_ratio_zero.const_mul (32*C)
  simp only [mul_zero] at ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hN.eventually hE,ht.eventually_lt_const (pow_pos hε 3),
    eventually_gt_atTop (0 : ℕ)] with N hEN hsmall hpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hpos
  have hb := (comparison_cube_le_cumulative_primeWinnerEnergy N).trans
    (mul_le_mul_of_nonneg_left hEN (by positivity))
  have hcube : |((risingCount N : ℝ)-fallingCount N)/N|^3 ≤
      (32*C)*((primeWinnerLabels (2*N)).card : ℝ)/N := by
    rw [abs_div,abs_of_pos hNr,div_pow]
    apply (div_le_iff₀ (pow_pos hNr 3)).mpr
    convert hb using 1 <;> push_cast <;> field_simp <;> ring
  simp only [dist_zero_right,Real.norm_eq_abs]
  by_contra h
  have hpow := pow_le_pow_left₀ hε.le (le_of_not_gt h) 3
  have hs : (32*C)*((primeWinnerLabels (2*N)).card : ℝ)/N < ε^3 := by
    simpa only [mul_div_assoc] using hsmall
  linarith

#print axioms unit_prefix_cube_le_square_sum
#print axioms comparison_cube_le_cumulative_primeWinnerEnergy
#print axioms density_of_quadratic_cumulative_primeWinnerEnergy
end Erdos371
