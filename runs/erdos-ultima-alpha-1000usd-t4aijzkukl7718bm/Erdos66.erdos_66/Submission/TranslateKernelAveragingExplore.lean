import Submission.UniversalKernelAccuracyExplore
import Submission.PrefixFaithfulParabolaLiftExplore

/-! Exact averaging of arbitrary old sets over all translates. This removes
an old flatness hypothesis in a finite product-group lift, but does not
construct an infinite natural-number set. -/
namespace Erdos66TranslateKernelAveraging
open Erdos66OriginRepair Erdos66PrefixFaithfulParabolaLift
  Erdos66UniformColorMoments Erdos66UniformSelection Erdos66ActualColorRootTransfer
  Erdos66UniversalKernelAccuracy Erdos66DisjointPaletteAssembly
open scoped Classical
set_option maxHeartbeats 1600000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma sum_pairCount (A B : Finset G) :
    (∑ z : G, pairCount A B z) = A.card * B.card := by
  simp only [pairCount, Finset.card_filter]
  rw [Finset.sum_comm]
  have he (a : G) : (∑ z : G, if z - a ∈ B then 1 else 0) = B.card := by
    rw [← Equiv.sum_comp (Equiv.addRight a)]
    simp
  simp_rw [he]
  simp

lemma sum_translated_pairCount (A B : Finset G) (a z : G) :
    (∑ b : G, pairCount (shiftSet A a) (shiftSet B b) z) = A.card * B.card := by
  simp_rw [pairCount_shiftSet]
  rw [← Equiv.sum_comp (Equiv.subLeft (z - a))]
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  exact sum_pairCount A B

lemma sum_all_translated_pairCount (A B : Finset G) (z : G) :
    (∑ a : G, ∑ b : G, pairCount (shiftSet A a) (shiftSet B b) z) =
      Fintype.card G * (A.card * B.card) := by
  simp_rw [sum_translated_pairCount]
  simp

lemma translated_kernel_mean (A : Finset G) (z : G) :
    kernelMean (coarseKernel (shiftSet A) z) = (A.card : ℝ) ^ 2 / Fintype.card G := by
  have hs : (∑ a : G, ∑ b : G,
      (pairCount (shiftSet A a) (shiftSet A b) z : ℝ)) =
        (Fintype.card G : ℝ) * ((A.card : ℝ) * A.card) := by
    exact_mod_cast sum_all_translated_pairCount A A z
  have hg : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [kernelMean, mean, coarseKernel, Fintype.sum_prod_type,
    Fintype.card_prod, Nat.cast_mul, hs]
  field_simp

variable {p : ℕ} [Fact p.Prime]

/-- One palette works for every later old set, even when its own sum counts
are completely nonuniform. The target mean remembers only its cardinality. -/
theorem exists_universal_translate_averaging (hp : p ≠ 2) (h m : ℕ)
    (hh : h ^ 2 + 4 * h + 2 < p) (e : Fin h ≃ G × Fin m) (hpos : 1 ≤ h)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsize : 680 * (Fintype.card G : ℝ) ^ 4 ≤ ε ^ 2 * (h : ℝ)) :
    ∃ P : Fin h → Finset (ZMod p × ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (A : Finset G) (z : G) (t s : ZMod p),
        |(pairCount (assembly P (fun i ↦ shiftSet A (e i).1))
            (assembly P (fun i ↦ shiftSet A (e i).1)) ((t, s), z) : ℝ) -
          (h : ℝ) ^ 2 * ((A.card : ℝ) ^ 2 / Fintype.card G)| ≤
            ε * (h : ℝ) ^ 2 * ((A.card : ℝ) ^ 2 / Fintype.card G) := by
  obtain ⟨P, hP, hb⟩ := exists_universal_actual_accuracy (α := G) (H := G)
    hp h m hh e hpos ε hε hsize
  refine ⟨P, hP, fun A z t s ↦ ?_⟩
  simpa only [translated_kernel_mean] using hb (shiftSet A) z t s

end Erdos66TranslateKernelAveraging
