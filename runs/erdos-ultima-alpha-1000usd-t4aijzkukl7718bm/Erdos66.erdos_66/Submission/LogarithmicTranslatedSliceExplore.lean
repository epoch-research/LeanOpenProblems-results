import Submission.TranslatedSliceLiftExplore
import Submission.NestedDifferencePaletteExplore
import Submission.LogTuningExplore

/-! Logarithmically tuned finite product-group extensions of arbitrary old
slices. These sets have no asserted natural-number transition estimates. -/
namespace Erdos66LogarithmicTranslatedSlice
open Filter Erdos66OriginRepair Erdos66PrefixFaithfulParabolaLift
  Erdos66TranslatedSliceLift Erdos66DisjointPaletteAssembly
  Erdos66NestedDifferencePalette Erdos66LogTuning
open scoped Classical Topology
set_option maxHeartbeats 1800000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- An arbitrary nonempty old slice can be retained exactly while all finite
product-group sums are retuned to a prescribed logarithmic coefficient.
Every old residue is also attained outside the retained slice. -/
theorem exists_logarithmic_translated_slice (A : Finset G) (hA : A.Nonempty)
    (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ M : ℕ, N₀ < M ∧ 1 < M ∧ ∃ _ : NeZero M,
      ∃ B : Finset (ZMod M × G),
        (∀ a : G, (0, a) ∈ B ↔ a ∈ A) ∧
        (∀ a : G, ∃ z : ZMod M, z ≠ 0 ∧ (z, a) ∈ B) ∧
        (∀ z : ZMod M × G,
          |(pairCount B B z : ℝ) / Real.log ((Fintype.card G * M : ℕ) : ℝ) - c| < ε) := by
  let g : ℕ := Fintype.card G
  have hg : 0 < g := Fintype.card_pos
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  let D : ℝ := (g : ℝ) * (A.card : ℝ) ^ 2
  have hD : 0 < D := by
    have ha : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
    dsimp [D]
    positivity
  let τ := min (ε / 8) (1 / 4)
  let δ := min (1 / 4) (ε / (8 * (c + 1)))
  have hτ : 0 < τ := lt_min (by positivity) (by norm_num)
  have hτe : τ ≤ ε / 8 := min_le_left _ _
  have hτ1 : τ ≤ 1 / 4 := min_le_right _ _
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
  have hδe : δ * (c + 1) ≤ ε / 8 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 8 * (c + 1))).mp
      (min_le_right (1 / 4) (ε / (8 * (c + 1))))
    change δ * (8 * (c + 1)) ≤ ε at ht
    nlinarith
  have hlogg : 0 ≤ Real.log (g : ℝ) := Real.log_natCast_nonneg g
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (log_nat_atTop.eventually_gt_atTop
      (max 1 (max (c * Real.log (g : ℝ) / τ) (8 * (g : ℝ) / ε))))
  obtain ⟨M, hMN, hModd, hM, μ, hμ, htune, Q, hQdis, hQ⟩ :=
    exists_logarithmic_disjoint_cyclic_palette (c / D) (τ / D) δ
      (by positivity) (by positivity) hδ g (max N₀ (max K 2))
  letI := hM
  have hM2 : 1 < M := by omega
  letI : Fact (1 < M) := ⟨hM2⟩
  let P : G → Finset (ZMod M) := fun i ↦ Q (Fintype.equivFin G i)
  have hPdis : Pairwise (fun i j ↦ Disjoint (P i) (P j)) := by
    intro i j hij
    exact hQdis (fun hh ↦ hij ((Fintype.equivFin G).injective hh))
  have hP (i j : G) (z : ZMod M) :
      |(pairCount (P i) (P j) z : ℝ) - μ| ≤ δ * μ :=
    hQ (Fintype.equivFin G i) (Fintype.equivFin G j) z
  have hPnz (i : G) : ∃ z ∈ P i, z ≠ 0 := by
    have hh := (abs_le.mp (hP i i 1)).1
    have hmul := mul_le_mul_of_nonneg_right hδ1 hμ.le
    have hpos : (0 : ℝ) < pairCount (P i) (P i) 1 := by linarith
    exact exists_nonzero_member_of_positive_count (P i) 1 one_ne_zero
      (by exact_mod_cast hpos)
  let B := replaceZeroSlice (assembly P (shiftSet A)) A
  have herr (z : ZMod M) (q : G) :
      |(pairCount B B (z, q) : ℝ) - μ * D| ≤ δ * μ * D + 2 * (g : ℝ) :=
    translated_slice_lift_error P hPdis A μ δ hP z q
  have hbig := hK M (by omega)
  have hlogM : 0 < Real.log (M : ℝ) := by
    have hh := (le_max_left 1 _).trans_lt hbig
    linarith
  have hbigτ : c * Real.log (g : ℝ) / τ < Real.log (M : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hbig
  have hbige : 8 * (g : ℝ) / ε < Real.log (M : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hbig
  let l : ℝ := Real.log ((g * M : ℕ) : ℝ)
  have hlex : l = Real.log (g : ℝ) + Real.log (M : ℝ) := by
    dsimp [l]
    rw [Nat.cast_mul, Real.log_mul hgr.ne' (by positivity)]
  have hl : 0 < l := by rw [hlex]; linarith
  have hMl : Real.log (M : ℝ) ≤ l := by rw [hlex]; linarith
  have ht : |μ * D / Real.log (M : ℝ) - c| < τ := by
    have hh := mul_lt_mul_of_pos_right htune hD
    rw [show |μ / Real.log (M : ℝ) - c / D| * D =
      |(μ / Real.log (M : ℝ) - c / D) * D| by
        rw [abs_mul, abs_of_pos hD]] at hh
    have he : (μ / Real.log (M : ℝ) - c / D) * D =
        μ * D / Real.log (M : ℝ) - c := by field_simp
    rw [he, div_mul_cancel₀ _ hD.ne'] at hh
    exact hh
  have hmain : |μ * D / l - c| < 2 * τ := by
    have hratio : 0 ≤ Real.log (M : ℝ) / l := by positivity
    have hratio1 : Real.log (M : ℝ) / l ≤ 1 := (div_le_one hl).mpr hMl
    have hfirst : |(μ * D / Real.log (M : ℝ) - c) * (Real.log (M : ℝ) / l)| < τ := by
      rw [abs_mul, abs_of_nonneg hratio]
      exact (mul_le_of_le_one_right (abs_nonneg _) hratio1).trans_lt ht
    have hsecond : |c * Real.log (g : ℝ) / l| < τ := by
      rw [abs_of_nonneg (by positivity)]
      apply (div_lt_iff₀ hl).mpr
      have hh := (div_lt_iff₀ hτ).mp hbigτ
      nlinarith [mul_le_mul_of_nonneg_left hMl hτ.le]
    have he : μ * D / l - c =
        (μ * D / Real.log (M : ℝ) - c) * (Real.log (M : ℝ) / l) -
          c * Real.log (g : ℝ) / l := by
      rw [hlex]
      field_simp
      ring
    rw [he]
    exact (abs_sub _ _).trans_lt (by linarith)
  have hpatch : 2 * (g : ℝ) / l < ε / 4 := by
    apply (div_lt_iff₀ hl).mpr
    have hh := (div_lt_iff₀ hε).mp hbige
    nlinarith [mul_le_mul_of_nonneg_left hMl hε.le]
  have hmeanup : μ * D / l < c + 1 := by
    have hh := (abs_lt.mp hmain).2
    linarith
  have hnoise : δ * (μ * D / l) < ε / 8 :=
    (mul_lt_mul_of_pos_left hmeanup hδ).trans_le hδe
  refine ⟨M, by omega, hM2, hM, B, ?_, ?_, ?_⟩
  · exact replaceZeroSlice_zero _ A
  · exact translated_slice_lift_full_projection P A hA hPnz
  · rintro ⟨z, q⟩
    change |(pairCount B B (z, q) : ℝ) / l - c| < ε
    have hdiv : |(pairCount B B (z, q) : ℝ) / l - μ * D / l| ≤
        δ * (μ * D / l) + 2 * (g : ℝ) / l := by
      rw [← sub_div, abs_div, abs_of_pos hl]
      have hh := div_le_div_of_nonneg_right (herr z q) hl.le
      convert hh using 1
      ring
    have hh := abs_sub_le ((pairCount B B (z, q) : ℝ) / l) (μ * D / l) c
    linarith

end Erdos66LogarithmicTranslatedSlice
