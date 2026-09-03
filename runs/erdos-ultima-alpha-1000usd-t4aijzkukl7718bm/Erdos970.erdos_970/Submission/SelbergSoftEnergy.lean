import Submission.SelbergCost

/-! Positive lower-kernel energy from a truncated linear additive profile. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def softProfile (u : ι → ℝ) (L : ℝ) (Q : Finset ι) : ℝ :=
  max (L - ∑ i ∈ Q, u i) 0

lemma softProfile_nonneg (u : ι → ℝ) (L : ℝ) (Q : Finset ι) :
    0 ≤ softProfile u L Q := le_max_right _ _

lemma softProfile_le (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (L : ℝ) (hL : 0 ≤ L)
    (Q : Finset ι) : softProfile u L Q ≤ L := by
  exact max_le (sub_le_self L (sum_nonneg (fun i _ => hu i))) hL

lemma softProfile_difference (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (L : ℝ)
    (Q : Finset ι) (i : ι) (hi : i ∉ Q) :
    |softProfile u L Q - softProfile u L (insert i Q)| ≤ u i := by
  unfold softProfile
  rw [sum_insert hi]
  have hh := abs_max_sub_max_le_abs (L - ∑ j ∈ Q, u j) (L - (u i + ∑ j ∈ Q, u j)) 0
  have he : (L - ∑ j ∈ Q, u j) - (L - (u i + ∑ j ∈ Q, u j)) = u i := by ring
  simpa only [he, abs_of_nonneg (hu i)] using hh

lemma sum_weight_pos (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1) :
    0 < ∑ Q : Finset ι, weight q Q :=
  sum_pos (fun Q _ => weight_pos q hq Q) univ_nonempty

lemma one_le_sum_weight (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1) :
    1 ≤ ∑ Q : Finset ι, weight q Q := by
  have hh := single_le_sum (s := univ) (f := weight q)
    (fun Q _ => (weight_pos q hq Q).le) (mem_univ ∅)
  simpa only [weight, prod_empty] using hh

lemma weighted_additive_sum (q u : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1) :
    (∑ Q : Finset ι, weight q Q * ∑ i ∈ Q, u i) =
      (∑ Q : Finset ι, weight q Q) * ∑ i, q i * u i := by
  have he (Q : Finset ι) : (∑ i ∈ Q, u i) = ∑ i : ι, if i ∈ Q then u i else 0 := by
    simp
  simp_rw [he, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have hh := sum_supersets_weight q hq {i}
  simp only [singleton_subset_iff, prod_singleton] at hh
  calc
    _ = (∑ Q : Finset ι, if i ∈ Q then weight q Q else 0) * u i := by
      rw [sum_mul]
      apply sum_congr rfl
      intro Q hQ
      split_ifs <;> ring
    _ = _ := by rw [hh]; ring

/-- Weighted Cauchy-Schwarz without square roots in the conclusion. -/
lemma weighted_square_sum (w f : Finset ι → ℝ) (hw : ∀ Q, 0 ≤ w Q) :
    (∑ Q : Finset ι, w Q * f Q) ^ 2 ≤
      (∑ Q : Finset ι, w Q) * ∑ Q : Finset ι, w Q * f Q ^ 2 := by
  apply sum_sq_le_sum_mul_sum_of_sq_eq_mul (s := univ)
    (r := fun Q => w Q * f Q) (f := w) (g := fun Q => w Q * f Q ^ 2)
    (fun Q _ => hw Q) (fun Q _ => mul_nonneg (hw Q) (sq_nonneg _))
  intro Q hQ
  ring

/-- The mean of a truncated affine profile is controlled by the first additive
moment, and its Dirichlet cost by the second additive moment. -/
theorem softProfile_energy_lower (q u : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (hu : ∀ i, 0 ≤ u i)
    (L M V : ℝ) (hML : M ≤ L) (hmean : (∑ i, q i * u i) ≤ M)
    (hsecond : (∑ i, q i * u i ^ 2) ≤ V) :
    (∑ Q : Finset ι, weight q Q) * ((L - M) ^ 2 - V) ≤
      kernelEnergy q (fun Q => weight q Q * softProfile u L Q) := by
  let W := ∑ Q : Finset ι, weight q Q
  have hW : 0 < W := sum_weight_pos q hq
  have hmean' : W * (L - M) ≤ ∑ Q : Finset ι, weight q Q * softProfile u L Q := by
    calc
      _ ≤ W * (L - ∑ i, q i * u i) := mul_le_mul_of_nonneg_left (by linarith) hW.le
      _ = ∑ Q : Finset ι, weight q Q * (L - ∑ i ∈ Q, u i) := by
        simp only [mul_sub, sum_sub_distrib, ← sum_mul, weighted_additive_sum q u hq]
        rfl
      _ ≤ _ := sum_le_sum (fun Q _ => mul_le_mul_of_nonneg_left
        (le_max_left _ _) (weight_pos q hq Q).le)
  have hcauchy := weighted_square_sum (weight q) (softProfile u L)
    (fun Q => (weight_pos q hq Q).le)
  have hsquare : W * (L - M) ^ 2 ≤
      ∑ Q : Finset ι, weight q Q * softProfile u L Q ^ 2 := by
    have hnon : 0 ≤ W * (L - M) := mul_nonneg hW.le (sub_nonneg.mpr hML)
    have hh := sq_le_sq₀ hnon (hnon.trans hmean') |>.mpr hmean'
    change _ ≤ W * _ at hcauchy
    nlinarith
  have hdir : (∑ i, q i * ∑ Q ∈ (univ.erase i).powerset,
      weight q Q * (softProfile u L Q - softProfile u L (insert i Q)) ^ 2) ≤ W * V := by
    calc
      _ ≤ ∑ i, q i * (W * u i ^ 2) := by
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (hq i).1.le
        calc
          _ ≤ ∑ Q ∈ (univ.erase i).powerset, weight q Q * u i ^ 2 := by
            apply sum_le_sum
            intro Q hQ
            apply mul_le_mul_of_nonneg_left _ (weight_pos q hq Q).le
            have hh := softProfile_difference u hu L Q i (not_mem_of_erase_powerset hQ)
            nlinarith [sq_abs (softProfile u L Q - softProfile u L (insert i Q)), hu i,
              abs_nonneg (softProfile u L Q - softProfile u L (insert i Q))]
          _ ≤ ∑ Q : Finset ι, weight q Q * u i ^ 2 :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun Q _ _ =>
              mul_nonneg (weight_pos q hq Q).le (sq_nonneg _))
          _ = W * u i ^ 2 := by rw [← sum_mul]
      _ = W * ∑ i, q i * u i ^ 2 := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsecond hW.le
  rw [kernelEnergy_weighted q hq]
  change W * _ ≤ _
  nlinarith only [hsquare, hdir]

/-- Convenient explicit constants for the first and second moment bounds. -/
theorem softProfile_energy_pos (q u : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (hu : ∀ i, 0 ≤ u i)
    (M : ℝ) (hM : 0 < M)
    (hmean : (∑ i, q i * u i) ≤ (65 / 64) * M)
    (hsecond : (∑ i, q i * u i ^ 2) ≤ (65 / 64) * M ^ 2) :
    M ^ 2 ≤ kernelEnergy q (fun Q => weight q Q * softProfile u ((5 / 2) * M) Q) := by
  have hh := softProfile_energy_lower q u hq hu ((5 / 2) * M) ((65 / 64) * M)
    ((65 / 64) * M ^ 2) (by linarith) hmean hsecond
  have hW := one_le_sum_weight q hq
  have hcoef : M ^ 2 ≤ ((5 / 2) * M - (65 / 64) * M) ^ 2 - (65 / 64) * M ^ 2 := by
    nlinarith [sq_nonneg M]
  have hcoef0 := (sq_nonneg M).trans hcoef
  have hmul := mul_le_mul_of_nonneg_right hW hcoef0
  nlinarith only [hh, hcoef, hmul]

#print axioms softProfile_energy_lower
#print axioms softProfile_energy_pos
end Erdos970.FiniteSelberg
