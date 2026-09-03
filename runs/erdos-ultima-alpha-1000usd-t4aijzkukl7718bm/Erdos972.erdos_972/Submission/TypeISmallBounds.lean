import Submission.TypeIPolynomial

/-! L1 bounds for the isolated small-input terms on both coordinates. -/
namespace Erdos972TypeISmallBounds

open Finset ArithmeticFunction
open Erdos972Vaughan Erdos972PrimePowerError Erdos972ChebyshevRowMean

lemma cutoff_mangoldt_sum_le (V N : ℕ) : (∑ n ∈ Ioc 0 N, cutoff Λ V n) ≤ Chebyshev.psi V := by
  have he : (∑ n ∈ Ioc 0 N, cutoff Λ V n) = ∑ n ∈ Ioc 0 (min N V), vonMangoldt n := by
    simp only [cutoff_apply, ← sum_filter]
    congr 1
    ext n
    simp only [mem_filter, mem_Ioc, le_min_iff]
    tauto
  rw [he]
  have hh := Chebyshev.psi_mono (Nat.cast_le.mpr (min_le_right N V))
  simpa only [Chebyshev.psi, Nat.floor_natCast] using hh

lemma cutoff_mangoldt_output_sum_le {α : ℝ} (hα : 1 ≤ α) (V N : ℕ) :
    (∑ n ∈ Ioc 0 N, cutoff Λ V (floorMul α n)) ≤ Chebyshev.psi V := by
  classical
  calc
    _ = ∑ q ∈ (Ioc 0 N).image (floorMul α), cutoff Λ V q := by
      rw [sum_image (fun n hn m hm he => (floorMul_strictMono hα).injective he)]
    _ ≤ ∑ q ∈ Ioc 0 (floorMul α N), cutoff Λ V q := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
        exact mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hn).1,
          (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2⟩
      · intro q hq hqn
        exact cutoff_vonMangoldt_nonneg V q
    _ ≤ _ := cutoff_mangoldt_sum_le V _

#print axioms cutoff_mangoldt_output_sum_le

end Erdos972TypeISmallBounds
