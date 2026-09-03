import Submission.FiniteBoundarySelectionExplore

/-! Small boundary envelopes, prefix discrepancy, and summable representation
costs retained for one infinite set. -/
namespace Erdos66BoundaryCompactness
open AdditiveCombinatorics Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential Erdos66TripleIntersectionMean Erdos66FiniteBernoulli
  Erdos66Compactness Erdos66PrefixBalancedUpperLimit Erdos66Generating
open scoped Classical Topology
set_option maxHeartbeats 2200000

 theorem exists_summable_costs_with_boundary (p : ℕ → ℝ) (N₀ : ℕ → ℕ)
    (cost : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ j n, Continuous (cost j n))
    (hpos : ∀ j n x, 0 ≤ cost j n x)
    (hfinite : ∀ L : ℕ, ∃ A : Set ℕ,
      (∀ k ≤ L, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
      (∀ j ≤ L, ∀ n ≤ L, N₀ j ≤ n →
        ((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ) ≤ 3*ell n) ∧
      (∀ j ≤ L, ∀ K ≤ L, (∑ n∈Finset.range K, cost j n (sumRep A n)) ≤ 1)) :
    ∃ A : Set ℕ,
      (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
      (∀ j n, N₀ j ≤ n →
        ((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ) ≤ 3*ell n) ∧
      (∀ j, Summable (fun n ↦ cost j n (sumRep A n))) := by
  let C : ℕ → Set (ℕ → Bool) := fun L ↦ {f |
    (∀ k ≤ L, |encodedMass f k-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
    (∀ j ≤ L, ∀ n ≤ L, N₀ j ≤ n →
      ((j:ℝ)+1)*encodedBoundary f (cutoff j) n ≤ 3*ell n) ∧
    (∀ j ≤ L, ∀ K ≤ L, (∑ n∈Finset.range K, cost j n (encodedRep f n)) ≤ 1)}
  have hclosed (L : ℕ) : IsClosed (C L) := by
    dsimp only [C]
    simp only [Set.setOf_and]
    apply IsClosed.inter
    · simp only [Set.setOf_forall]
      exact isClosed_iInter (fun k ↦ isClosed_iInter (fun _ ↦
        isClosed_le ((continuous_encodedMass k).sub continuous_const).abs continuous_const))
    · apply IsClosed.inter
      · simp only [Set.setOf_forall]
        repeat' (apply isClosed_iInter; intro)
        exact isClosed_le (continuous_const.mul (continuous_encodedBoundary _ _)) continuous_const
      · simp only [Set.setOf_forall]
        refine isClosed_iInter (fun j ↦ isClosed_iInter (fun _ ↦
          isClosed_iInter (fun K ↦ isClosed_iInter (fun _ ↦ ?_))))
        exact isClosed_le (continuous_finset_sum _ (fun n _ ↦
          (hcont j n).comp (continuous_encodedRep n))) continuous_const
  have hne (L : ℕ) : (C L).Nonempty := by
    obtain ⟨A,hA,ht,hcost⟩ := hfinite L
    refine ⟨fun i ↦ decide (i∈A),?_,?_,?_⟩
    · intro k hk
      simpa only [encodedMass_decide] using hA k hk
    · intro j hj n hn hN₀
      rw [encodedBoundary_decide]
      exact ht j hj n hn hN₀
    · intro j hj K hK
      simpa only [encodedRep_decide] using hcost j hj K hK
  have hmono (L : ℕ) : C (L+1)⊆C L := by
    intro f hf
    exact ⟨fun k hk ↦ hf.1 k (by omega),
      fun j hj n hn hN₀ ↦ hf.2.1 j (by omega) n (by omega) hN₀,
      fun j hj K hK ↦ hf.2.2 j (by omega) K (by omega)⟩
  obtain ⟨f,hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    hmono hne (hclosed 0).isCompact hclosed
  let A : Set ℕ := {i | f i=true}
  refine ⟨A,?_,?_,?_⟩
  · intro k
    have hh := (Set.mem_iInter.mp hf k).1 k le_rfl
    have he : encodedMass f k=∑ i∈Finset.range k, indicator A i := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [bit,indicator,A]
      cases f i <;> simp
    rwa [he] at hh
  · intro j n hN₀
    have hh := (Set.mem_iInter.mp hf (max j n)).2.1 j (le_max_left _ _) n (le_max_right _ _) hN₀
    simpa only [encodedBoundary_eq] using hh
  · intro j
    apply summable_of_sum_range_le (c := 1) (fun n ↦ hpos j n _)
    intro K
    have hh := (Set.mem_iInter.mp hf (max j K)).2.2 j (le_max_left _ _) K (le_max_right _ _)
    simpa only [encodedRep_eq_sumRep] using hh

end Erdos66BoundaryCompactness
