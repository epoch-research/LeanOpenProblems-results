import Submission.CompactnessExplore

/-! Compactness selection for countably many nonnegative representation costs. -/
namespace Erdos66SummableCostCompactness
open Erdos66Compactness AdditiveCombinatorics
open scoped Classical Topology

/-- Uniform finite bounds for each row of costs yield one set with all rows
summable. The cost functions and their unit budgets are fixed before L. -/
theorem exists_summable_costs (cost : ℕ → ℕ → ℝ → ℝ)
    (hcont : ∀ j n, Continuous (cost j n))
    (hpos : ∀ j n x, 0 ≤ cost j n x)
    (hfinite : ∀ L : ℕ, ∃ A : Set ℕ, ∀ j ≤ L, ∀ K ≤ L,
      (∑ n ∈ Finset.range K, cost j n (sumRep A n)) ≤ 1) :
    ∃ A : Set ℕ, ∀ j, Summable (fun n ↦ cost j n (sumRep A n)) := by
  let C : ℕ → Set (ℕ → Bool) := fun L ↦ {f | ∀ j ≤ L, ∀ K ≤ L,
    (∑ n ∈ Finset.range K, cost j n (encodedRep f n)) ≤ 1}
  have hclosed (L : ℕ) : IsClosed (C L) := by
    dsimp only [C]
    simp only [Set.setOf_forall]
    refine isClosed_iInter (fun j ↦ isClosed_iInter (fun _ ↦
      isClosed_iInter (fun K ↦ isClosed_iInter (fun _ ↦ ?_))))
    exact isClosed_le (continuous_finset_sum _ (fun n _ ↦
      (hcont j n).comp (continuous_encodedRep n))) continuous_const
  have hne (L : ℕ) : (C L).Nonempty := by
    obtain ⟨A,hA⟩ := hfinite L
    refine ⟨fun i ↦ decide (i∈A),fun j hj K hK ↦ ?_⟩
    simp_rw [encodedRep_decide]
    exact hA j hj K hK
  have hmono (L : ℕ) : C (L+1) ⊆ C L := by
    intro f hf j hj K hK
    exact hf j (by omega) K (by omega)
  obtain ⟨f,hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    hmono hne (hclosed 0).isCompact hclosed
  refine ⟨{i | f i=true},fun j ↦ summable_of_sum_range_le (c := 1) (fun n ↦ hpos j n _) (fun K ↦ ?_)⟩
  have hh := Set.mem_iInter.mp hf (max j K) j (le_max_left _ _) K (le_max_right _ _)
  simpa only [encodedRep_eq_sumRep] using hh

end Erdos66SummableCostCompactness
