import Submission.SpectralSkewSymmetry

/-! Adding finitely many powers of each defining character converts a small
Bohr radius into radius 1/2, with an explicit linear rank cost. -/
namespace Erdos3BohrPowerNormalization
open Finset Erdos3FiniteBohr Erdos3BohrCovering
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def powerFamily (C : Finset (AddChar G ℂ)) (m : ℕ) : Finset (AddChar G ℂ) :=
  (C ×ˢ range (m+1)).image (fun p ↦ p.2 • p.1)

lemma powerFamily_card (C : Finset (AddChar G ℂ)) (m : ℕ) :
    (powerFamily C m).card ≤ (m+1)*C.card := by
  exact card_image_le.trans_eq (by rw [card_product,card_range,mul_comm])

/-- A phase whose first m powers remain within 1/2 of one must itself be
within 1/m of one. A geometric sum avoids any choice of argument branch. -/
lemma small_powers_force_small (z : ℂ) {m : ℕ} (hm : 0 < m)
    (h : ∀ j ≤ m, ‖z^j-1‖ ≤ 1/2) : ‖z-1‖ ≤ 1/(m : ℝ) := by
  let S : ℂ := ∑ j ∈ range m, z^j
  have hre : (m : ℝ)/2 ≤ S.re := by
    have hj (j : ℕ) (hj : j ∈ range m) : (1/2 : ℝ) ≤ (z^j).re := by
      have hh := (Complex.abs_re_le_norm (z^j-1)).trans (h j (Nat.le_of_lt (mem_range.mp hj)))
      have hl := (abs_le.mp hh).1
      simp only [Complex.sub_re,Complex.one_re] at hl
      linarith
    calc
      _ = ∑ _j ∈ range m, (1/2 : ℝ) := by simp; ring
      _ ≤ ∑ j ∈ range m, (z^j).re := sum_le_sum hj
      _ = _ := by simp only [S,Complex.re_sum]
  have hnorm : (m : ℝ)/2 ≤ ‖S‖ := hre.trans (Complex.re_le_norm _)
  have hp : ‖z-1‖*‖S‖ ≤ 1/2 := by
    rw [← norm_mul]
    simpa only [S,mul_geom_sum] using h m le_rfl
  have hh := mul_le_mul_of_nonneg_left hnorm (norm_nonneg (z-1))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (le_div_iff₀ hmR).mpr
  nlinarith

lemma powerFamily_bohr_subset (C : Finset (AddChar G ℂ)) {m : ℕ} (hm : 0 < m) :
    bohr (powerFamily C m) (1/2) ⊆ bohr C (1/(m : ℝ)) := by
  intro x hx
  apply mem_bohr.mpr
  intro χ hχ
  apply small_powers_force_small (χ x) hm
  intro j hj
  have hm : j • χ ∈ powerFamily C m := mem_image.mpr
    ⟨(χ,j),mem_product.mpr ⟨hχ,mem_range.mpr (by omega)⟩,rfl⟩
  simpa only [AddChar.nsmul_apply] using mem_bohr.mp hx (j • χ) hm

noncomputable def radiusPower (r : ℝ) : ℕ := ⌈1/r⌉₊+1

lemma radiusPower_pos (r : ℝ) : 0 < radiusPower r := by unfold radiusPower; omega

lemma radiusPower_bound {r : ℝ} (hr : 0 < r) : 1/(radiusPower r : ℝ) ≤ r := by
  have hp : (0 : ℝ) < radiusPower r := by exact_mod_cast radiusPower_pos r
  have hh : 1/r ≤ (radiusPower r : ℝ) := by
    apply (Nat.le_ceil _).trans
    simp only [radiusPower,Nat.cast_add,Nat.cast_one]
    exact le_add_of_nonneg_right (by norm_num)
  apply (div_le_iff₀ hp).mpr
  have he := (div_le_iff₀ hr).mp hh
  nlinarith

/-- Radius normalization with an explicit character-count bound. -/
theorem normalize_bohr_radius (C : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r) :
    ∃ E : Finset (AddChar G ℂ), E.card ≤ (radiusPower r+1)*C.card ∧
      bohr E (1/2) ⊆ bohr C r := by
  exact ⟨powerFamily C (radiusPower r),powerFamily_card C _,
    (powerFamily_bohr_subset C (radiusPower_pos r)).trans (bohr_mono C (radiusPower_bound hr))⟩

#print axioms normalize_bohr_radius
end Erdos3BohrPowerNormalization
