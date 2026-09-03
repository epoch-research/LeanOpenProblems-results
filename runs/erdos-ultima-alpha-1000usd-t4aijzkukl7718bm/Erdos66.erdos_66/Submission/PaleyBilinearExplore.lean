import Submission.CharacterEnergyExplore

/-! Uniform bilinear bounds for translates of the quadratic character.
These finite-field estimates do not settle the natural-number conjecture. -/
namespace Erdos66PaleyBilinear
open Erdos66CharacterEnergy
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma shiftSum_set_energy (hF : ringChar F ≠ 2) (V : Finset F) :
    (∑ x : F, (shiftSum V id x)^2) =
      (Fintype.card F : ℤ) * V.card - (V.card : ℤ)^2 := by
  rw [shiftSum_energy_identity hF]
  simp only [id_eq, Finset.sum_ite_eq]
  simp

noncomputable def bilinear (U V : Finset F) (q : F) : ℤ :=
  ∑ u ∈ U, ∑ v ∈ V, quadraticChar F (q-u-v)

lemma bilinear_comm (U V : Finset F) (q : F) :
    bilinear U V q = bilinear V U q := by
  unfold bilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  ring

lemma bilinear_sq_le (hF : ringChar F ≠ 2) (U V : Finset F) (q : F) :
    (bilinear U V q)^2 ≤
      (U.card : ℤ) * ((Fintype.card F : ℤ) * V.card - (V.card : ℤ)^2) := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := U)
    (f := fun u ↦ shiftSum V id (q-u))
  have he : bilinear U V q = ∑ u ∈ U, shiftSum V id (q-u) := by
    simp [bilinear, shiftSum]
  rw [he]
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  calc
    (∑ u ∈ U, (shiftSum V id (q-u))^2) ≤
        ∑ u : F, (shiftSum V id (q-u))^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ x : F, (shiftSum V id x)^2 :=
      (Equiv.subLeft q).sum_comp (fun x ↦ (shiftSum V id x)^2)
    _ = _ := shiftSum_set_energy hF V

lemma bilinear_sq_le_card (hF : ringChar F ≠ 2) (U V : Finset F) (q : F) :
    (bilinear U V q)^2 ≤ (Fintype.card F : ℤ) * U.card * V.card := by
  have hh := bilinear_sq_le hF U V q
  have hn := mul_nonneg (Nat.cast_nonneg U.card : (0 : ℤ) ≤ U.card)
    (sq_nonneg (V.card : ℤ))
  nlinarith

lemma bilinear_real_abs_le (hF : ringChar F ≠ 2) (U V : Finset F) (q : F) :
    |(bilinear U V q : ℝ)| ≤
      Real.sqrt ((Fintype.card F : ℝ) * U.card * V.card) := by
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
  rw [sq_abs]
  exact_mod_cast bilinear_sq_le_card hF U V q

end Erdos66PaleyBilinear
