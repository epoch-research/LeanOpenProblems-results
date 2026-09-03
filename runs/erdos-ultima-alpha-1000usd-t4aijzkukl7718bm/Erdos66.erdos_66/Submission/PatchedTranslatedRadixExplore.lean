import Submission.TranslatedRadixCarryExplore

/-! Exact preservation of a natural prefix in the translate-averaging radix
lift. The representation estimates in this file are still cyclic counts. -/
namespace Erdos66PatchedTranslatedRadix
open Erdos66OriginRepair Erdos66PrefixFaithfulParabolaLift
  Erdos66TranslatedRadixCarry Erdos66RectangularRadix Erdos66CyclicPrefixPatch
open scoped Classical
set_option maxHeartbeats 1600000

variable (L M : ℕ) [NeZero L] [NeZero M]

noncomputable def patchedRadix (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M)) :
    Finset (ZMod (L * M)) :=
  patch (L * M) (radixAssembly L M (shiftSet A) P) {n : ℕ | (n : ZMod L) ∈ A} L

lemma patchedRadix_prefix (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M))
    (n : ℕ) (hn : n < L) :
    (n : ZMod (L * M)) ∈ patchedRadix L M A P ↔ (n : ZMod L) ∈ A := by
  have hM := NeZero.pos M
  have hnM : n < L * M := by nlinarith
  rw [patchedRadix, patch_agree, ZMod.val_natCast_of_lt hnM, if_pos hn]
  rfl

lemma patchedRadix_off (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M))
    (a : ZMod L) (z : ZMod M) (hz : z ≠ 0) :
    encode L M (a, z) ∈ patchedRadix L M A P ↔
      encode L M (a, z) ∈ radixAssembly L M (shiftSet A) P := by
  have hzval : 0 < z.val := ZMod.val_pos.mpr hz
  have hlarge : ¬ a.val + L * z.val < L := by nlinarith
  rw [patchedRadix, patch_agree, encode_val, if_neg hlarge]

lemma patchedRadix_error (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (μ δ : ℝ)
    (hb : ∀ i j z, |(pairCount (P i) (P j) z : ℝ) - μ| ≤ δ * μ)
    (z : ZMod (L * M)) :
    |(pairCount (patchedRadix L M A P) (patchedRadix L M A P) z : ℝ) -
      μ * ((L : ℝ) * (A.card : ℝ) ^ 2)| ≤
        δ * μ * ((L : ℝ) * (A.card : ℝ) ^ 2) + 2 * (L : ℝ) := by
  have hp := patch_error (L * M) (radixAssembly L M (shiftSet A) P)
    {n : ℕ | (n : ZMod L) ∈ A} L z
  change |(pairCount (patchedRadix L M A P) (patchedRadix L M A P) z : ℝ) -
      pairCount (radixAssembly L M (shiftSet A) P) (radixAssembly L M (shiftSet A) P) z| ≤
        2 * (L : ℝ) at hp
  have he := translated_radix_error L M A P hP μ δ hb z
  exact (abs_sub_le _ (pairCount (radixAssembly L M (shiftSet A) P)
    (radixAssembly L M (shiftSet A) P) z : ℝ) _).trans (by linarith)

lemma patchedRadix_full_projection (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M))
    (hA : A.Nonempty) (hP : ∀ i : ZMod L, ∃ z ∈ P i, z ≠ 0) (a : ZMod L) :
    ∃ z : ZMod M, z ≠ 0 ∧ encode L M (a, z) ∈ patchedRadix L M A P := by
  obtain ⟨b, hb⟩ := hA
  obtain ⟨z, hz, hz0⟩ := hP (a - b)
  refine ⟨z, hz0, (patchedRadix_off L M A P a z hz0).mpr ?_⟩
  rw [mem_radixAssembly]
  refine ⟨a - b, ?_, hz⟩
  rw [mem_shiftSet]
  simpa only [sub_sub_cancel] using hb

end Erdos66PatchedTranslatedRadix
