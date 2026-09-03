import Submission.SampledQuadraticAverage

/-! One Bohr window works for every stable quadratic test of bounded rank.
The width depends only on the rank bound and the preselected tolerance. -/
namespace Erdos3CommonQuadraticWindow
open Finset Erdos3FiniteBohr Erdos3RelativeStableBohr Erdos3BohrCovering
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

noncomputable def commonWidth (R z : ℕ) : ℝ := (1/64)/(windowDenominator R z : ℝ)

lemma commonWidth_pos (R : ℕ) {z : ℕ} (hz : 0 < z) : 0 < commonWidth R z := by
  unfold commonWidth
  exact div_pos (by norm_num) (by exact_mod_cast windowDenominator_pos R hz)

lemma windowDenominator_mono {d R : ℕ} (hd : d ≤ R) (z : ℕ) :
    windowDenominator d z ≤ windowDenominator R z := by
  unfold windowDenominator
  gcongr

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma commonWidth_le_relative (D : Finset (AddChar G ℂ)) {R z : ℕ}
    (hD : D.card ≤ R) (hz : 0 < z) {r : ℝ} (hr : 1/64 ≤ r) :
    commonWidth R z ≤ relativeWidth D z r := by
  unfold commonWidth relativeWidth
  calc
    _ ≤ (1/64 : ℝ)/(windowDenominator D.card z : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num)
        (by exact_mod_cast windowDenominator_pos D.card hz)
      exact_mod_cast windowDenominator_mono hD z
    _ ≤ _ := div_le_div_of_nonneg_right hr (Nat.cast_nonneg _)

noncomputable def commonCharacters {I : Type*} [Fintype I]
    (D : I → Finset (AddChar G ℂ)) : Finset (AddChar G ℂ) := univ.biUnion D

lemma commonCharacters_card {I : Type*} [Fintype I]
    (D : I → Finset (AddChar G ℂ)) {R : ℕ} (hD : ∀ i, (D i).card ≤ R) :
    (commonCharacters D).card ≤ Fintype.card I*R := by
  calc
    _ ≤ ∑ i : I, (D i).card := card_biUnion_le
    _ ≤ ∑ _i : I, R := sum_le_sum (fun i _ ↦ hD i)
    _ = _ := by simp

lemma common_window_subset {I : Type*} [Fintype I]
    (D : I → Finset (AddChar G ℂ)) (r : I → ℝ) {R z : ℕ}
    (hD : ∀ i, (D i).card ≤ R) (hz : 0 < z) (hr : ∀ i, 1/64 ≤ r i) (i : I) :
    bohr (commonCharacters D) (commonWidth R z) ⊆ bohr (D i) (relativeWidth (D i) z (r i)) := by
  intro x hx
  apply mem_bohr.mpr
  intro χ hχ
  have hm : χ ∈ commonCharacters D := mem_biUnion.mpr ⟨i,mem_univ _,hχ⟩
  exact (mem_bohr.mp hx χ hm).trans (commonWidth_le_relative (D i) (hD i) hz (hr i))

/-- Explicit size estimate for the common window. The exponent is linear in
the total character rank, and no individual stable radius needs to be known. -/
theorem common_window_card_bound {I : Type*} [Fintype I]
    (D : I → Finset (AddChar G ℂ)) {R z : ℕ}
    (hD : ∀ i, (D i).card ≤ R) (hz : 0 < z) :
    Fintype.card G ≤ (256*windowDenominator R z+1)^(2*(Fintype.card I*R))*
      (bohr (commonCharacters D) (commonWidth R z)).card := by
  have hq : 0 < 128*windowDenominator R z := by
    exact Nat.mul_pos (by decide) (windowDenominator_pos R hz)
  have h := card_bohr_lower (commonCharacters D) hq
  have he : 2/((128*windowDenominator R z : ℕ) : ℝ) = commonWidth R z := by
    unfold commonWidth
    push_cast
    ring
  rw [he] at h
  calc
    _ ≤ (2*(128*windowDenominator R z)+1)^(2*(commonCharacters D).card)*
        (bohr (commonCharacters D) (commonWidth R z)).card := h
    _ ≤ _ := by
      have hc := commonCharacters_card D hD
      rw [show 2*(128*windowDenominator R z)+1 = 256*windowDenominator R z+1 by ring]
      gcongr
      omega

#print axioms common_window_subset
#print axioms common_window_card_bound
end Erdos3CommonQuadraticWindow
