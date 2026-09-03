import Submission.NaturalPositivePatternExplore

/-! Compactness jointly retains arbitrary positive finite-coordinate pattern
budgets, all prefix discrepancies, and summable representation costs. -/
namespace Erdos66PositivePatternCompactness
open AdditiveCombinatorics Erdos66NaturalPositivePattern Erdos66FiniteBernoulli
  Erdos66Compactness Erdos66PrefixBalancedUpperLimit Erdos66Generating
open scoped Classical Topology
set_option maxHeartbeats 1600000

 theorem exists_summable_costs_with_patterns (p : ℕ → ℝ) (P : ℕ → Pattern)
    (cost : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ j n, Continuous (cost j n))
    (hpos : ∀ j n x, 0 ≤ cost j n x)
    (hfinite : ∀ L : ℕ, ∃ A : Set ℕ,
      (∀ k ≤ L, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
      (∑ j∈Finset.range L, (P j).value (fun i ↦ decide (i∈A))) ≤ 1 ∧
      (∀ j ≤ L, ∀ K ≤ L, (∑ n∈Finset.range K, cost j n (sumRep A n)) ≤ 1)) :
    ∃ A : Set ℕ,
      (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
      (∀ S : Finset ℕ, (∑ j∈S, (P j).value (fun i ↦ decide (i∈A))) ≤ 1) ∧
      (∀ j, Summable (fun n ↦ cost j n (sumRep A n))) := by
  let C : ℕ → Set (ℕ → Bool) := fun L ↦ {f |
    (∀ k ≤ L, |encodedMass f k-(∑ i∈Finset.range k, p i)| ≤ 1) ∧
    (∑ j∈Finset.range L, (P j).value f) ≤ 1 ∧
    (∀ j ≤ L, ∀ K ≤ L, (∑ n∈Finset.range K, cost j n (encodedRep f n)) ≤ 1)}
  have hclosed (L : ℕ) : IsClosed (C L) := by
    dsimp only [C]
    simp only [Set.setOf_and]
    apply IsClosed.inter
    · simp only [Set.setOf_forall]
      exact isClosed_iInter (fun k ↦ isClosed_iInter (fun _ ↦
        isClosed_le ((continuous_encodedMass k).sub continuous_const).abs continuous_const))
    · apply IsClosed.inter
      · exact isClosed_le (continuous_finset_sum _ (fun j _ ↦ (P j).continuous_value)) continuous_const
      · simp only [Set.setOf_forall]
        refine isClosed_iInter (fun j ↦ isClosed_iInter (fun _ ↦
          isClosed_iInter (fun K ↦ isClosed_iInter (fun _ ↦ ?_))))
        exact isClosed_le (continuous_finset_sum _ (fun n _ ↦
          (hcont j n).comp (continuous_encodedRep n))) continuous_const
  have hne (L : ℕ) : (C L).Nonempty := by
    obtain ⟨A,hA,hP,hcost⟩ := hfinite L
    refine ⟨fun i ↦ decide (i∈A),?_,hP,?_⟩
    · intro k hk
      simpa only [encodedMass_decide] using hA k hk
    · intro j hj K hK
      simpa only [encodedRep_decide] using hcost j hj K hK
  have hmono (L : ℕ) : C (L+1)⊆C L := by
    intro f hf
    refine ⟨fun k hk ↦ hf.1 k (by omega),?_,fun j hj K hK ↦ hf.2.2 j (by omega) K (by omega)⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ ↦ (P j).value_nonneg f)).trans hf.2.1
  obtain ⟨f,hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    hmono hne (hclosed 0).isCompact hclosed
  let A : Set ℕ := {i | f i=true}
  have hbits : (fun i ↦ decide (i∈A))=f := by funext i; simp [A]
  refine ⟨A,?_,?_,?_⟩
  · intro k
    have hh := (Set.mem_iInter.mp hf k).1 k le_rfl
    have he : encodedMass f k=∑ i∈Finset.range k, indicator A i := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [bit,indicator,A]
      cases f i <;> simp
    rwa [he] at hh
  · intro S
    simp only [A,Set.mem_setOf_eq,Bool.decide_eq_true]
    have hs : S ⊆ Finset.range (S.sup id+1) := by
      intro j hj
      have hh := Finset.le_sup (f := id) hj
      exact Finset.mem_range.mpr (by change j ≤ S.sup id at hh; omega)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun j _ _ ↦ (P j).value_nonneg f)).trans
      (Set.mem_iInter.mp hf (S.sup id+1)).2.1
  · intro j
    apply summable_of_sum_range_le (c := 1) (fun n ↦ hpos j n _)
    intro K
    have hh := (Set.mem_iInter.mp hf (max j K)).2.2 j (le_max_left _ _) K (le_max_right _ _)
    simpa only [encodedRep_eq_sumRep] using hh

end Erdos66PositivePatternCompactness
