import Submission.TranslateKernelAveragingExplore
import Submission.CyclicPrefixPatchExplore

/-! A finite product-group lift that averages old translates, then replaces
one slice exactly. No natural-number scale transition is claimed. -/
namespace Erdos66TranslatedSliceLift
open Erdos66OriginRepair Erdos66PrefixFaithfulParabolaLift
  Erdos66TranslateKernelAveraging Erdos66DisjointPaletteAssembly
open scoped Classical
set_option maxHeartbeats 1800000

variable {F G : Type*} [AddCommGroup F] [DecidableEq F]
  [AddCommGroup G] [DecidableEq G] [Fintype G]

lemma translated_assembly_error (P : G → Finset F)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (A : Finset G) (μ δ : ℝ)
    (hb : ∀ i j z, |(pairCount (P i) (P j) z : ℝ) - μ| ≤ δ * μ)
    (z : F) (q : G) :
    |(pairCount (assembly P (shiftSet A)) (assembly P (shiftSet A)) (z, q) : ℝ) -
      μ * ((Fintype.card G : ℝ) * (A.card : ℝ) ^ 2)| ≤
        δ * μ * ((Fintype.card G : ℝ) * (A.card : ℝ) ^ 2) := by
  have hs : (∑ i : G, ∑ j : G,
      (pairCount (shiftSet A i) (shiftSet A j) q : ℝ)) =
        (Fintype.card G : ℝ) * (A.card : ℝ) ^ 2 := by
    simpa only [pow_two] using
      (show (∑ i : G, ∑ j : G,
          (pairCount (shiftSet A i) (shiftSet A j) q : ℝ)) =
        (Fintype.card G : ℝ) * ((A.card : ℝ) * A.card) by
          exact_mod_cast sum_all_translated_pairCount A A q)
  rw [assembly_pairCount P hP]
  push_cast
  rw [← hs, Finset.mul_sum]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← sub_mul]
  calc
    _ ≤ ∑ i : G, ∑ j : G,
        |((pairCount (P i) (P j) z : ℝ) - μ) *
          (pairCount (shiftSet A i) (shiftSet A j) q : ℝ)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : G, ∑ j : G,
        δ * μ * (pairCount (shiftSet A i) (shiftSet A j) q : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg
        (pairCount (shiftSet A i) (shiftSet A j) q) :
          (0 : ℝ) ≤ (pairCount (shiftSet A i) (shiftSet A j) q : ℝ))]
      exact mul_le_mul_of_nonneg_right (hb i j z) (Nat.cast_nonneg _)
    _ = _ := rfl

noncomputable def replaceZeroSlice (B : Finset (F × G)) (A : Finset G) :
    Finset (F × G) :=
  B.filter (fun z ↦ z.1 ≠ 0) ∪ ({0} ×ˢ A)

omit [AddCommGroup G] [Fintype G] in
lemma replaceZeroSlice_zero (B : Finset (F × G)) (A : Finset G) (a : G) :
    (0, a) ∈ replaceZeroSlice B A ↔ a ∈ A := by
  simp [replaceZeroSlice]

omit [AddCommGroup G] [Fintype G] in
lemma replaceZeroSlice_off (B : Finset (F × G)) (A : Finset G)
    (z : F × G) (hz : z.1 ≠ 0) :
    z ∈ replaceZeroSlice B A ↔ z ∈ B := by
  simp only [replaceZeroSlice, Finset.mem_union, Finset.mem_filter,
    Finset.mem_product, Finset.mem_singleton, hz, false_and, or_false]
  exact and_iff_left hz

lemma replaceZeroSlice_error (B : Finset (F × G)) (A : Finset G) (z : F × G) :
    |(pairCount (replaceZeroSlice B A) (replaceZeroSlice B A) z : ℝ) -
      pairCount B B z| ≤ 2 * (Fintype.card G : ℝ) := by
  have he := Erdos66CyclicPrefixPatch.count_error_of_agree_off
    (replaceZeroSlice B A) B (({0} : Finset F) ×ˢ (Finset.univ : Finset G))
    (fun x hx ↦ replaceZeroSlice_off B A x (by
      intro hz
      exact hx (Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr hz, Finset.mem_univ _⟩))) z
  simpa only [Finset.card_product, Finset.card_singleton, Finset.card_univ,
    one_mul] using he

lemma translated_slice_lift_error (P : G → Finset F)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (A : Finset G) (μ δ : ℝ)
    (hb : ∀ i j z, |(pairCount (P i) (P j) z : ℝ) - μ| ≤ δ * μ)
    (z : F) (q : G) :
    |(pairCount (replaceZeroSlice (assembly P (shiftSet A)) A)
        (replaceZeroSlice (assembly P (shiftSet A)) A) (z, q) : ℝ) -
      μ * ((Fintype.card G : ℝ) * (A.card : ℝ) ^ 2)| ≤
        δ * μ * ((Fintype.card G : ℝ) * (A.card : ℝ) ^ 2) +
          2 * (Fintype.card G : ℝ) := by
  exact (abs_sub_le _ (pairCount (assembly P (shiftSet A))
    (assembly P (shiftSet A)) (z, q) : ℝ) _).trans (by
      linarith [replaceZeroSlice_error (assembly P (shiftSet A)) A (z, q),
        translated_assembly_error P hP A μ δ hb z q])

lemma exists_nonzero_member_of_positive_count (B : Finset F) (z : F)
    (hz : z ≠ 0) (hb : 0 < pairCount B B z) :
    ∃ x ∈ B, x ≠ 0 := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hb
  obtain ⟨hxB, hzxB⟩ := Finset.mem_filter.mp hx
  by_cases hx0 : x = 0
  · exact ⟨z - x, hzxB, by simpa [hx0] using hz⟩
  · exact ⟨x, hxB, hx0⟩

/-- Every old residue is reached away from the retained slice, not merely
inside the slice. This does not require the old set itself to be flat. -/
lemma translated_slice_lift_full_projection (P : G → Finset F) (A : Finset G)
    (hA : A.Nonempty) (hP : ∀ i : G, ∃ z ∈ P i, z ≠ 0) (q : G) :
    ∃ z : F, z ≠ 0 ∧
      (z, q) ∈ replaceZeroSlice (assembly P (shiftSet A)) A := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨z, hz, hz0⟩ := hP (q - a)
  refine ⟨z, hz0, (replaceZeroSlice_off _ _ (z, q) hz0).mpr ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨q - a, Finset.mem_univ _, Finset.mem_product.mpr ⟨hz, ?_⟩⟩
  rw [mem_shiftSet]
  simpa only [sub_sub_cancel] using ha

end Erdos66TranslatedSliceLift
